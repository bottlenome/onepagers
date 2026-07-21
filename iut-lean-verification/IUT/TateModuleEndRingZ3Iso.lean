/-
  IUT/TateModuleEndRingZ3Iso.lean — TRZ（柱A7: **End(ℤ₃(1)) ≅ ℤ₃ の本物の環同型**——
  tmer が指数族表示の上で確立した End(T) の環演算を、柱A2 の実 ℤ₃ 環オブジェクト
  `z3 = zpRing 3` への**明示逆写像つき両側環同型**（`z3vRingEquivData trzEndRing z3`・
  ∃ 不要・choice-free）として本物に接続する。設計:
  audit/pillar-A7-endring-z3-iso-detail-2026-07-20.md（判定: 到達可能・新イディオム 0））

  ── 主要成果の分類: **[実／(a) 昇格]**（骨格・模型・代理でなく、tmer の指数表示上の
     End 環（正直な限定 (1)(2) で「z3 との環同型接続・End の抽象環束ねは未」と名指し）を
     **実対象同士の環同型**へ昇格する。TRZ-0〜5:
      (i)   TRZ-0: 代表元抽出 `trzRep`（`Quot.lift (a % m).toNat`・Finiteness の
            `zmod_finite` イディオムの写経・choice-free）と Nat↔Int mod 橋。
      (ii)  TRZ-1: **End(ℤ₃(1)) の可換環束ね** `trzEndRing : CRing`（add=`tmerAdd`・
            mul=`Hom.comp`・mul_comm は `tme_endo_ext`+`tmer_comp_comm`・left_distrib は
            各点 `f.map_mul`）——tmer 限定 (2) の discharge。
      (iii) TRZ-2: **順方向環準同型** `trzToZ3 : RingHom trzEndRing z3`
            （level n で Quot.mk (tmeChar f n)・整合は `tme_char_compat` の
            mod 3^{i+1} ⊋ mod 3^i 過剰供給・+,·,1 は `tmer_char_add`/
            `tmer_char_comp`/`tmer_char_id`）。
      (iv)  TRZ-3: **単射** `trz_inj`（level n+1 成分＋`tme_char_compat` の 1 段シフト＋
            `tme_endo_ext`）。
      (v)   TRZ-4: **明示逆写像** `trzFromZ3 = tmiPowHom ∘ 代表元族`（関数レベル・
            Prop-∃ に隠さない）と両往復 `trz_from_to`（ψ∘φ=id・`tmi_pow_char`）/
            `trz_to_from`（φ∘ψ=id・`trzRep_mk` roundtrip）。
      (vi)  TRZ-5: capstone `trz_ring_iso : z3vRingEquivData trzEndRing z3`
            （既存の汎用環同型構造体を再利用・逆写像も RingHom として束ねる）
            ——tmer 限定 (1) の discharge。

  **complete_pct 影響**: A7（実円分剛性）——tmer/tme/tmi が 3 ファイル連続で名指しした
  後続ターゲット「End(ℤ₃(1)) ≅ ℤ₃（実 z3）の環同型」を正面 discharge し、柱A7 の End 側と
  柱A2 の実付値環側という**別建設の実対象同士の同定**を閉じる。予測 s_A7 0.57→0.58
  （設計 §4 中央値・数値は独立監査が確定・柱A 表示は動かない見込み）。

  正直な限定（§4 規約により消さない・弱めない・sorry で埋めない）:
   (1) **mono-theta 円分剛性（[EtTh]）は本スライスの外・依然 0**: 本環同型は ℤ₃^×
       不定性を**殺さない**（Aut(T) ≅ ℤ₃^× の CHARACTERIZE の環版完成であって KILL では
       ない）。kill は mod-9 実装済（q9mb/crk）＋ mod-27 設計のみで、full ℤ₃^× kill・
       実 wild 円分塔は依然 0——**A7 は ≤0.60〜0.62 帯の帽子のまま**（設計 §4）。
   (2) **p = 3 固定・円分切片限定・位相未形式化・幾何側不在**: T=ℤ₃(1)・
       G=Gal(ℚ(ζ_{3^∞})/ℚ)。実 G_{ℚ₃}・実 G_ℚ・一般素数 p・K̄/幾何的 cyclotome は 0。
       `trzToZ3` の連続性（limitTopology 間の位相同型）は主張しない。
   (3) **Q₃ 体・付値の同変性までは束ねない**: z3 は A2 の実付値環オブジェクトだが、
       本スライスは環同型のみ。Galois 同変性は `tmi_act_char` の帰結として別スライス。
   (4) tmz/tme/tmi/tmer の他の正直な限定は**一切消さない・弱めない**。tmer 限定 (1)(2)
       のみが「名指しされた本物を建てたことによる討ち取り型 discharge」として閉じる。

  全て選択公理不使用（propext/Quot.sound のみ・逆写像も Quot.lift による関数）。
  禁止タクティク（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
  field_simp）不使用。3^ℓ は omega に生で渡さない（`zpu_pow_pos`/`zpu_pow_dvd`/
  `zpu_one_lt`/`pow_dvd_mono` 経由）。新規ファイル 1 個のみ（共有ファイルは親が統合）。
  prefix `trz`。
-/
import IUT.TateModuleEndoRing
import IUT.TateModuleIndeterminacy
import IUT.Zp3ValuationRing
import IUT.Finiteness

namespace IUT

/-! ## TRZ-0: 代表元抽出と Nat↔Int mod 橋（`zmod_finite` イディオムの写経・choice-free） -/

/-- **TRZ-0a: Nat mod 等式 → Int ∣ 差** — A ≡ B (mod m) の Nat 剰余等式を
    modCong 側の Int 可除性へ翻訳する（`dvd_of_emod_eq`＋`Int.natCast_emod`）。 -/
theorem trz_dvd_of_nat_mod {m A B : Nat} (h : A % m = B % m) :
    ((m : Nat) : Int) ∣ ((A : Nat) : Int) - ((B : Nat) : Int) := by
  apply dvd_of_emod_eq
  rw [← Int.natCast_emod A m, ← Int.natCast_emod B m, h]

/-- **TRZ-0b: 1 段強い合同の弱化** — tmeChar 系の mod 3^{n+1} 合同（tme/tmer が供給）は
    z3 の level n（mod 3^n）が要求する可除性を**過剰供給**する（3^n ∣ 3^{n+1} 経由）。 -/
theorem trz_dvd_of_mod_succ {n A B : Nat} (h : A % 3 ^ (n + 1) = B % 3 ^ (n + 1)) :
    ((3 ^ n : Nat) : Int) ∣ ((A : Nat) : Int) - ((B : Nat) : Int) :=
  Int.dvd_trans (Int.ofNat_dvd.mpr (zpu_pow_dvd (Nat.le_succ n))) (trz_dvd_of_nat_mod h)

/-- **TRZ-0c: choice-free 代表元抽出** — `zmod m` の Quot 類から非負剰余代表 Nat を返す
    **関数**。well-definedness は `emod_eq_of_dvd`（`Finiteness.lean` の `zmod_finite`
    M17-5a と一字一句同じイディオム・選択公理不使用）。 -/
def trzRep (m : Nat) (q : (zmod m).carrier) : Nat :=
  Quot.lift (fun a : Int => (a % ((m : Nat) : Int)).toNat)
    (fun a b hab => by
      show (a % ((m : Nat) : Int)).toNat = (b % ((m : Nat) : Int)).toNat
      rw [emod_eq_of_dvd hab]) q

/-- **TRZ-0d: 代表元抽出の計算形** — Nat キャスト類の代表は Nat 剰余そのもの。 -/
theorem trzRep_cast (m A : Nat) :
    trzRep m (Quot.mk (modCong m).rel ((A : Nat) : Int)) = A % m := by
  show (((A : Nat) : Int) % ((m : Nat) : Int)).toNat = A % m
  rw [← Int.natCast_emod A m]
  rfl

/-- **TRZ-0e: roundtrip** — 代表元を Quot.mk し直すと元の類に戻る
    （`Int.emod_nonneg`/`Int.toNat_of_nonneg`＋`modCong_emod`）。 -/
theorem trzRep_mk (m : Nat) (hm : 0 < m) (q : (zmod m).carrier) :
    Quot.mk (modCong m).rel ((trzRep m q : Nat) : Int) = q := by
  induction q using Quot.ind; rename_i a
  have hne : ((m : Nat) : Int) ≠ 0 := by omega
  have ht : ((((a % ((m : Nat) : Int)).toNat : Nat)) : Int) = a % ((m : Nat) : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg a hne)
  show Quot.mk (modCong m).rel (((a % ((m : Nat) : Int)).toNat : Nat) : Int)
     = Quot.mk (modCong m).rel a
  rw [ht]
  exact Quot.sound (dvd_sub_symm (modCong_emod m a))

/-! ## TRZ-1: End(ℤ₃(1)) の可換環束ね（tmer 限定 (2) の discharge） -/

/-- **TRZ-1a: 可換群の inv-of-product** — inv (a·b) = inv a · inv b
    （`tmer_mul4` 4 項入れ替え＋`Grp.inv_eq_of_mul_eq_one`）。 -/
theorem trz_inv_mul (G : Grp) (hc : ∀ a b, G.mul a b = G.mul b a) (a b : G.carrier) :
    G.inv (G.mul a b) = G.mul (G.inv a) (G.inv b) := by
  have h : G.mul (G.mul a b) (G.mul (G.inv a) (G.inv b)) = G.one := by
    rw [tmer_mul4 G hc a b (G.inv a) (G.inv b), G.mul_inv a, G.mul_inv b, G.one_mul]
  exact (G.inv_eq_of_mul_eq_one h).symm

/-- **TRZ-1b: 点ごとの逆元自己準同型**（End の加法逆元）。map_mul は可換群 T の
    inv-of-product（`trz_inv_mul`＋`tmer_limit_comm`）。 -/
def trzNeg (f : Hom tmzLimit tmzLimit) : Hom tmzLimit tmzLimit where
  map := fun y => tmzLimit.inv (f.map y)
  map_mul := fun y z => by
    show tmzLimit.inv (f.map (tmzLimit.mul y z))
       = tmzLimit.mul (tmzLimit.inv (f.map y)) (tmzLimit.inv (f.map z))
    rw [f.map_mul y z]
    exact trz_inv_mul tmzLimit tmer_limit_comm (f.map y) (f.map z)

/-- **TRZ-1c（★）: End(ℤ₃(1)) は可換環** `trzEndRing : CRing` — carrier =
    `Hom tmzLimit tmzLimit`、加法 = 点ごと積 `tmerAdd`、乗法 = 合成 `Hom.comp`。
    加法公理は点ごと群律（`cra_hom_ext`）、mul_comm は `tme_endo_ext`＋`tmer_comp_comm`
    （End 完全分類の消費）、left_distrib は各点 `f.map_mul` そのもの。
    **tmer 正直限定 (2)「End の抽象環束ねは未」の discharge。** -/
def trzEndRing : CRing where
  carrier := Hom tmzLimit tmzLimit
  add := tmerAdd
  zero := tmerZero
  neg := trzNeg
  mul := fun f g => Hom.comp f g
  one := tmerId
  add_assoc := fun f g h =>
    cra_hom_ext _ _ (fun y => tmzLimit.mul_assoc (f.map y) (g.map y) (h.map y))
  zero_add := fun f => cra_hom_ext _ _ (fun y => tmzLimit.one_mul (f.map y))
  neg_add := fun f => cra_hom_ext _ _ (fun y => tmzLimit.inv_mul (f.map y))
  add_comm := fun f g => cra_hom_ext _ _ (fun y => tmer_limit_comm (f.map y) (g.map y))
  mul_assoc := fun _ _ _ => cra_hom_ext _ _ (fun _ => rfl)
  one_mul := fun _ => cra_hom_ext _ _ (fun _ => rfl)
  mul_comm := fun f g => tme_endo_ext _ _ (tmer_comp_comm f g)
  left_distrib := fun f g h =>
    cra_hom_ext _ _ (fun y => f.map_mul (g.map y) (h.map y))

/-! ## TRZ-2: 順方向環準同型 End(ℤ₃(1)) → z3 -/

/-- **TRZ-2a: 順方向の台関数** — level n で `Quot.mk (tmeChar f n)`。逆極限の整合性は
    既証明 `tme_char_compat`（mod 3^{i+1}）が padicSystem 3 の要求（mod 3^i）を
    **過剰供給**して閉じる（設計 §2 攻撃 1: 新しい極限構成・完備化は一切不要）。 -/
def trzToZ3Fun (f : Hom tmzLimit tmzLimit) : (Zp 3).carrier :=
  ⟨fun n => Quot.mk (modCong (3 ^ n)).rel ((tmeChar f n : Nat) : Int), by
    intro i j h
    show (zmodTrans (pow_dvd_mono 3 h)).map
        (Quot.mk (modCong (3 ^ j)).rel ((tmeChar f j : Nat) : Int))
      = Quot.mk (modCong (3 ^ i)).rel ((tmeChar f i : Nat) : Int)
    show Quot.mk (modCong (3 ^ i)).rel ((tmeChar f j : Nat) : Int)
       = Quot.mk (modCong (3 ^ i)).rel ((tmeChar f i : Nat) : Int)
    exact Quot.sound (trz_dvd_of_mod_succ (tme_char_compat h f))⟩

/-- **TRZ-2b: 加法保存** — End の加法（点ごと積）↦ z3 の加法（成分 zmod 加法）。
    level n の代表元計算に `tmer_char_add`（mod 3^{n+1}）を弱化して食わせる。 -/
theorem trzTo_add (f g : Hom tmzLimit tmzLimit) :
    trzToZ3Fun (tmerAdd f g) = z3.add (trzToZ3Fun f) (trzToZ3Fun g) := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (3 ^ n)).rel ((tmeChar (tmerAdd f g) n : Nat) : Int)
     = Quot.mk (modCong (3 ^ n)).rel
         (((tmeChar f n : Nat) : Int) + ((tmeChar g n : Nat) : Int))
  rw [← Int.natCast_add (tmeChar f n) (tmeChar g n)]
  exact Quot.sound (trz_dvd_of_mod_succ (tmer_char_add f g n))

/-- **TRZ-2c: 乗法保存** — End の乗法（合成）↦ z3 の乗法（成分 `zmodMul`）。
    `tmer_char_comp`（合成 = 指数積・mod 3^{n+1}）がそのまま供給（設計 §2 攻撃 4）。 -/
theorem trzTo_mul (f g : Hom tmzLimit tmzLimit) :
    trzToZ3Fun (Hom.comp f g) = z3.mul (trzToZ3Fun f) (trzToZ3Fun g) := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (3 ^ n)).rel ((tmeChar (Hom.comp f g) n : Nat) : Int)
     = Quot.mk (modCong (3 ^ n)).rel
         (((tmeChar f n : Nat) : Int) * ((tmeChar g n : Nat) : Int))
  rw [← Int.natCast_mul (tmeChar f n) (tmeChar g n)]
  exact Quot.sound (trz_dvd_of_mod_succ (tmer_char_comp f g n))

/-- **TRZ-2d: 単位保存** — 恒等 ↦ zpOne（`tmer_char_id`＋1 % 3^{n+1} = 1）。 -/
theorem trzTo_one : trzToZ3Fun tmerId = z3.one := by
  apply Subtype.ext
  funext n
  show Quot.mk (modCong (3 ^ n)).rel ((tmeChar tmerId n : Nat) : Int)
     = Quot.mk (modCong (3 ^ n)).rel (((1 : Nat) : Int))
  have h1 : tmeChar tmerId n % 3 ^ (n + 1) = 1 % 3 ^ (n + 1) := by
    rw [tmer_char_id n]
    exact (Nat.mod_eq_of_lt (zpu_one_lt (n + 1) (by omega))).symm
  exact Quot.sound (trz_dvd_of_mod_succ h1)

/-- **TRZ-2e（★）: 順方向は環準同型** `trzToZ3 : RingHom trzEndRing z3` —
    実 End 環から柱A2 の実 ℤ₃ 環オブジェクトへの本物の環準同型。 -/
def trzToZ3 : RingHom trzEndRing z3 where
  map := trzToZ3Fun
  map_add := trzTo_add
  map_mul := trzTo_mul
  map_one := trzTo_one

/-! ## TRZ-3: 単射性（1 段シフト論法・設計 §2 攻撃 2） -/

/-- **TRZ-3（★単射）** — φ f = φ g なら f = g。level n の z3 成分（mod 3^n）だけでは
    `tme_endo_ext` の要求（mod 3^{n+1}）に 1 段届かないが、**level n+1 成分**の一致
    （mod 3^{n+1}）を `tme_char_compat` の 1 段シフトで level n の指数へ引き戻して回収する。 -/
theorem trz_inj (f g : Hom tmzLimit tmzLimit)
    (h : trzToZ3Fun f = trzToZ3Fun g) : f = g := by
  apply tme_endo_ext
  intro n
  have hv : Quot.mk (modCong (3 ^ (n + 1))).rel ((tmeChar f (n + 1) : Nat) : Int)
      = Quot.mk (modCong (3 ^ (n + 1))).rel ((tmeChar g (n + 1) : Nat) : Int) := by
    show (trzToZ3Fun f).val (n + 1) = (trzToZ3Fun g).val (n + 1)
    rw [h]
  have hr := congrArg (trzRep (3 ^ (n + 1))) hv
  rw [trzRep_cast (3 ^ (n + 1)) (tmeChar f (n + 1)),
      trzRep_cast (3 ^ (n + 1)) (tmeChar g (n + 1))] at hr
  rw [← tme_char_compat (Nat.le_succ n) f, ← tme_char_compat (Nat.le_succ n) g]
  exact hr

/-! ## TRZ-4: 明示逆写像と両往復（設計 §2 攻撃 3・choice-free） -/

/-- **TRZ-4a: z3 元の整合指数族** — level n の指数 = `trzRep` で抽出した
    x.val (n+1) の代表（mod 3^{n+1}）。整合性は x の整合族性（`zmodTrans` は代表元保存）
    ＋ `trzRep_mk`/`trzRep_cast` の roundtrip 簿記。**Quot 類からの代表元選択は
    choice ではない**——`Quot.lift` の関数である（`zmod_finite` と同じイディオム）。 -/
def trzExpFam (x : (Zp 3).carrier) : TmiExpFam where
  a := fun n => trzRep (3 ^ (n + 1)) (x.val (n + 1))
  compat := by
    intro i j h
    have hmkj : Quot.mk (modCong (3 ^ (j + 1))).rel
        ((trzRep (3 ^ (j + 1)) (x.val (j + 1)) : Nat) : Int) = x.val (j + 1) :=
      trzRep_mk (3 ^ (j + 1)) (zpu_pow_pos (j + 1)) (x.val (j + 1))
    have hstep : (zmodTrans (pow_dvd_mono 3 (Nat.succ_le_succ h))).map (x.val (j + 1))
        = x.val (i + 1) := x.property (Nat.succ_le_succ h)
    have hdown : Quot.mk (modCong (3 ^ (i + 1))).rel
        ((trzRep (3 ^ (j + 1)) (x.val (j + 1)) : Nat) : Int) = x.val (i + 1) :=
      (congrArg (zmodTrans (pow_dvd_mono 3 (Nat.succ_le_succ h))).map hmkj).trans hstep
    have hmki : Quot.mk (modCong (3 ^ (i + 1))).rel
        ((trzRep (3 ^ (i + 1)) (x.val (i + 1)) : Nat) : Int) = x.val (i + 1) :=
      trzRep_mk (3 ^ (i + 1)) (zpu_pow_pos (i + 1)) (x.val (i + 1))
    have hr := congrArg (trzRep (3 ^ (i + 1))) (hdown.trans hmki.symm)
    rw [trzRep_cast (3 ^ (i + 1)) (trzRep (3 ^ (j + 1)) (x.val (j + 1))),
        trzRep_cast (3 ^ (i + 1)) (trzRep (3 ^ (i + 1)) (x.val (i + 1)))] at hr
    exact hr

/-- **TRZ-4b: 明示逆写像**（関数レベル・∃ 不要） — `tmiPowHom`（tmi TMI-1b）に
    代表元族を食わせるだけ。 -/
def trzFromZ3 (x : (Zp 3).carrier) : Hom tmzLimit tmzLimit :=
  tmiPowHom (trzExpFam x)

/-- **TRZ-4c（★左往復）: ψ∘φ = id** — End から z3 へ行って戻ると元の自己準同型。
    `tmi_pow_char`（構成と分類の往復）＋`trzRep_cast`＋`tme_char_compat` シフト
    ＋`tme_endo_ext`。 -/
theorem trz_from_to (f : Hom tmzLimit tmzLimit) : trzFromZ3 (trzToZ3Fun f) = f := by
  apply tme_endo_ext
  intro n
  have h1 : tmeChar (tmiPowHom (trzExpFam (trzToZ3Fun f))) n % 3 ^ (n + 1)
      = (trzExpFam (trzToZ3Fun f)).a n % 3 ^ (n + 1) :=
    tmi_pow_char (trzExpFam (trzToZ3Fun f)) n
  have h2 : (trzExpFam (trzToZ3Fun f)).a n = tmeChar f (n + 1) % 3 ^ (n + 1) :=
    trzRep_cast (3 ^ (n + 1)) (tmeChar f (n + 1))
  show tmeChar (tmiPowHom (trzExpFam (trzToZ3Fun f))) n % 3 ^ (n + 1)
     = tmeChar f n % 3 ^ (n + 1)
  rw [h1, h2, Nat.mod_mod_of_dvd (tmeChar f (n + 1)) (Nat.dvd_refl (3 ^ (n + 1))),
      tme_char_compat (Nat.le_succ n) f]

/-- **TRZ-4d（★右往復）: φ∘ψ = id** — z3 から End へ行って戻ると元の ℤ₃ 元。
    level n で `trzRep_mk` roundtrip を x.property で 1 段押し下げ、
    `tmi_pow_char` の mod 3^{n+1} 一致を mod 3^n へ弱化して合流。 -/
theorem trz_to_from (x : (Zp 3).carrier) : trzToZ3Fun (trzFromZ3 x) = x := by
  apply Subtype.ext
  funext n
  have hmk : Quot.mk (modCong (3 ^ (n + 1))).rel
      ((trzRep (3 ^ (n + 1)) (x.val (n + 1)) : Nat) : Int) = x.val (n + 1) :=
    trzRep_mk (3 ^ (n + 1)) (zpu_pow_pos (n + 1)) (x.val (n + 1))
  have hstep : (zmodTrans (pow_dvd_mono 3 (Nat.le_succ n))).map (x.val (n + 1))
      = x.val n := x.property (Nat.le_succ n)
  have hxdown : Quot.mk (modCong (3 ^ n)).rel
      ((trzRep (3 ^ (n + 1)) (x.val (n + 1)) : Nat) : Int) = x.val n :=
    (congrArg (zmodTrans (pow_dvd_mono 3 (Nat.le_succ n))).map hmk).trans hstep
  show Quot.mk (modCong (3 ^ n)).rel
      ((tmeChar (tmiPowHom (trzExpFam x)) n : Nat) : Int) = x.val n
  rw [← hxdown]
  exact Quot.sound (trz_dvd_of_mod_succ (tmi_pow_char (trzExpFam x) n))

/-! ## TRZ-5: capstone — End(ℤ₃(1)) ≅ ℤ₃ の両側環同型（tmer 限定 (1) の discharge） -/

/-- **TRZ-5a: 逆写像の加法保存**（両往復から標準導出・新しい計算なし）。 -/
theorem trzFrom_add (x y : (Zp 3).carrier) :
    trzFromZ3 (z3.add x y) = tmerAdd (trzFromZ3 x) (trzFromZ3 y) := by
  have h1 : trzToZ3Fun (tmerAdd (trzFromZ3 x) (trzFromZ3 y)) = z3.add x y := by
    rw [trzTo_add, trz_to_from x, trz_to_from y]
  rw [← h1, trz_from_to]

/-- **TRZ-5b: 逆写像の乗法保存**。 -/
theorem trzFrom_mul (x y : (Zp 3).carrier) :
    trzFromZ3 (z3.mul x y) = Hom.comp (trzFromZ3 x) (trzFromZ3 y) := by
  have h1 : trzToZ3Fun (Hom.comp (trzFromZ3 x) (trzFromZ3 y)) = z3.mul x y := by
    rw [trzTo_mul, trz_to_from x, trz_to_from y]
  rw [← h1, trz_from_to]

/-- **TRZ-5c: 逆写像の単位保存**。 -/
theorem trzFrom_one : trzFromZ3 z3.one = tmerId := by
  rw [← trzTo_one, trz_from_to]

/-- **TRZ-5d: 逆写像も環準同型** `trzFromZ3Hom : RingHom z3 trzEndRing`。 -/
def trzFromZ3Hom : RingHom z3 trzEndRing where
  map := trzFromZ3
  map_add := trzFrom_add
  map_mul := trzFrom_mul
  map_one := trzFrom_one

/-- **TRZ-5e（★★capstone）: End(ℤ₃(1)) ≅ ℤ₃ の本物の環同型** —
    `z3vRingEquivData trzEndRing z3`（既存の汎用環同型構造体・toFun/invFun とも RingHom・
    左右往復とも関数レベルで証明済・∃ も choice も不要）。[IUTchI] の基本事実
    End(ℤ₃(1)) ≅ ℤ₃ が、柱A7 の実 End 環と柱A2 の実付値環 z3 という**別建設の実対象
    同士の同定**として閉じる。tmer 限定 (1)(2)・tme 限定 (4)・tmi 限定 (4) の discharge。
    **正直: この同型は ℤ₃^× 不定性を殺さない（ヘッダ限定 (1)）。** -/
def trz_ring_iso : z3vRingEquivData trzEndRing z3 where
  toFun := trzToZ3
  invFun := trzFromZ3Hom
  left_inv := trz_from_to
  right_inv := trz_to_from

/-- **TRZ-5f: 全射性の消去形**（witness は明示逆写像・∃ は Prop ゴール内のみ）。 -/
theorem trz_surj (x : (Zp 3).carrier) : ∃ f : Hom tmzLimit tmzLimit, trzToZ3Fun f = x :=
  ⟨trzFromZ3 x, trz_to_from x⟩

end IUT
