/-
  IUT/BrauerInvariantFull.lean — M395F [実・本物・柱B]
  complete_pct 影響: 柱B で M365F の巡回不変量を Br(K)[n] の巡回代数生成部分群
    K^×/N の上で **本物の群同型 K^×/N ≅ (1/n)ℤ/ℤ** に昇格する。M365F は
    briInvDescended を「単射かつ全射」までで、両側逆写像 Hom は選択公理回避のため
    未構成（M267F 正直な限定 #2）としていた。本モジュールは切断
    (1/n)ℤ/ℤ → K^×/N を [c]↦[(π^c)]（v(π)=1 の素元冪）で **明示的 Hom** として構成し、
    briInvDescended との両側逆律を選択公理なしで証明する。よって巡回代数生成部分群上で
    inv は加法的・全単射・**明示逆を持つ真の同型**（M365F の単射性を単一巡回類から
    部分群全体へ締め、像がちょうど (1/n)ℤ/ℤ であることを示す）。
  正直な限定: 全 Br(K)≅ℚ/ℤ（Br(K) の**全**類が巡回代数＝局所類体論の主定理・非巡回類を
    含む）は依然 `bri_full_inv_hypothesis`（未導出 Prop 仮説）。本物で閉じたのは巡回代数
    **生成部分群** K^×/N ≅ ℤ/n であって全 Br(K) ではない。後続。

  ── 本物で閉じる中身（骨格のみでない）:
  * M395F-1 `brfQuot` — 巡回代数生成部分群の忠実模型 K^×/N（M365F の核 N=不分岐ノルム群
    による商）。`brfInv`＝M365F `briInvDescended`（降下不変量 K^×/N → (1/n)ℤ/ℤ）。
  * M395F-2 `brf_ker_pair`／`brf_section_wd` — 切断の well-defined 補題（第一成分の
    付値が n を割れば核 N に属す・mod n 合同なら同一剰余類）。
  * M395F-3 `brfSection` — **明示切断** (1/n)ℤ/ℤ → K^×/N、[c]↦[(c,1_O)]（素元冪の類）。
    選択公理を使わず本物の群準同型として構成（map_mul も本証明）。
  * M395F-4 `brf_section_left_inv`／`brf_section_right_inv` — inv∘sec=id・sec∘inv=id を
    **本証明**（両側逆律）。これで K^×/N ≅ (1/n)ℤ/ℤ が明示逆付きの真の同型に昇格。
  * M395F-5 `brf_inv_injective_subgroup` — 巡回代数生成**部分群全体**での inv 単射性を
    明示逆から再証明（M365F の単一巡回類上単射を部分群全体へ締める）。
    `brf_inv_additive`（部分群上で inv 加法的）・`brf_image_full`（像がちょうど (1/n)ℤ/ℤ）。
  * M395F-6 `brf_tame_symbol_eq_inv` — 従順 Hilbert 記号（M375F）と降下不変量の整合:
    (a, 標準単数)_n = inv([a])。記号値が「その生成する巡回類の不変量」に一致（本証明）。
  * M395F-7 capstone `BrauerInvariantFullData`/`brfFullData`/`brf_exists` と n=2 実例
    （素元 π の巡回類の inv=1/2≠0・従順記号経由の非自明性）。

  **正直な限定**（消去・弱化禁止）:
  1. **全 Br(K) ≅ ℚ/ℤ**（全類が巡回代数＝局所 CFT の主定理）は `bri_full_inv_hypothesis`
     （未導出 Prop 仮説）。本モジュールが本物にしたのは**巡回代数生成部分群** K^×/N
     ≅ ℤ/n の同型（明示逆付き）であって非巡回類を含む全 Br(K) ではない。
  2. K^× は分裂表示 `unitsModel U = ℤ × O_v^×`（M330F/M365F 規約）。素元冪の切断
     [c]↦[(c,1)] はこの分裂座標に依存する（真の相互律・完全 CFT は後続）。
  3. ℚ/ℤ は固定 n の n-捻れ (1/n)ℤ/ℤ ≅ ℤ/n（`zmod n`、有限レベル）。
     全 ℚ/ℤ = colim_n の余極限は範囲外。

  **選択公理不使用・sorry 皆無**: 全宣言の公理は [propext, Quot.sound] のみ。
  禁止タクティク不使用。一般名は `brf` 接頭辞で衝突回避。共有ファイル未変更。
-/
import IUT.BrauerInvariant
import IUT.TameSymbol
import IUT.QuotientGroup

namespace IUT

/-! ## M395F-1: 巡回代数生成部分群の忠実模型 K^×/N と降下不変量 -/

/-- **巡回代数生成部分群の模型**（M395F-1a）: K^×/N（N=M365F 不変量の核＝不分岐
    ノルム群）。Br(K)[n] のうち巡回代数が生成する部分群の忠実模型。 -/
abbrev brfQuot (U : Grp) (n : Nat) : Grp :=
  quotientGroupN (unitsModel U) (kerSubgroup (briInvCyclic U n))
    (ker_isNormal (briInvCyclic U n))

/-- **降下不変量**（M395F-1b）: K^×/N → (1/n)ℤ/ℤ（M365F `briInvDescended` の別名）。 -/
def brfInv (U : Grp) (n : Nat) : Hom (brfQuot U n) (briQZn n) :=
  briInvDescended U n

/-! ## M395F-2: 切断の well-defined 補題 -/

/-- **核判定**（M395F-2a）: 第一成分（付値）が n を割る元は核 N に属す。 -/
theorem brf_ker_pair (U : Grp) (n : Nat) (x : (unitsModel U).carrier)
    (h : ((n : Nat) : Int) ∣ x.1) : (kerSubgroup (briInvCyclic U n)).mem x := by
  show (briInvCyclic U n).map x = (briQZn n).one
  rw [briInvCyclic_apply]
  exact (bri_qzn_zero_iff n x.1).mpr h

/-- **切断の well-defined**（M395F-2b）: mod n 合同 a≡b なら (a,1),(b,1) は
    K^×/N で同一剰余類（第一成分の差 b−a が n で割れ核に属す）。 -/
theorem brf_section_wd (U : Grp) (n : Nat) (a b : Int) (hab : (modCong n).rel a b) :
    (normalCong (unitsModel U) (kerSubgroup (briInvCyclic U n))
        (ker_isNormal (briInvCyclic U n))).rel (a, U.one) (b, U.one) := by
  show (kerSubgroup (briInvCyclic U n)).mem
        ((unitsModel U).mul ((unitsModel U).inv (a, U.one)) (b, U.one))
  apply brf_ker_pair
  show ((n : Nat) : Int) ∣ ((unitsModel U).mul ((unitsModel U).inv (a, U.one)) (b, U.one)).1
  obtain ⟨k, hk⟩ := hab
  refine ⟨-k, ?_⟩
  show intGrp.mul (intGrp.inv a) b = ((n : Nat) : Int) * (-k)
  show (-a) + b = ((n : Nat) : Int) * (-k)
  rw [Int.mul_neg, ← hk]
  omega

/-! ## M395F-3: 明示切断 (1/n)ℤ/ℤ → K^×/N -/

/-- **明示切断**（M395F-3）: (1/n)ℤ/ℤ → K^×/N、[c]↦[(c,1_O)]（付値 c の素元冪 π^c の
    巡回類）。選択公理を使わず本物の群準同型として構成。降下不変量 `brfInv` の
    両側逆写像になる（次節）。 -/
def brfSection (U : Grp) (n : Nat) : Hom (briQZn n) (brfQuot U n) where
  map := Quot.lift
    (fun c => (Quot.mk _ ((c, U.one) : (unitsModel U).carrier) : (brfQuot U n).carrier))
    (fun a b hab => Quot.sound (brf_section_wd U n a b hab))
  map_mul := by
    intro x y
    induction x using Quot.ind; rename_i c
    induction y using Quot.ind; rename_i d
    show (Quot.mk (normalCong (unitsModel U) (kerSubgroup (briInvCyclic U n))
            (ker_isNormal (briInvCyclic U n))).rel
            (((c : Int) + d), U.one) : (brfQuot U n).carrier)
       = Quot.mk _ ((unitsModel U).mul ((c, U.one) : (unitsModel U).carrier) (d, U.one))
    apply congrArg (Quot.mk _)
    show (((c : Int) + d), U.one) = (((c : Int) + d), U.mul U.one U.one)
    rw [U.one_mul]

/-- 切断の明示式: sec([c]) = [(c, 1_O)]。 -/
theorem brfSection_apply (U : Grp) (n : Nat) (c : Int) :
    (brfSection U n).map (Quot.mk (modCong n).rel c)
      = Quot.mk _ ((c, U.one) : (unitsModel U).carrier) := rfl

/-! ## M395F-4: 両側逆律 inv∘sec=id・sec∘inv=id（明示同型） -/

/-- **左逆律**（M395F-4a）: inv(sec([c])) = [c]。素元冪 π^c の巡回類の不変量は
    v(π^c)=c mod n。 -/
theorem brf_section_left_inv (U : Grp) (n : Nat) :
    ∀ y, (brfInv U n).map ((brfSection U n).map y) = y := by
  intro y
  induction y using Quot.ind; rename_i c
  rfl

/-- **右逆律**（M395F-4b）: sec(inv([x])) = [x]。任意類 [x=(k,u)] は付値 k の
    素元冪類 [(k,1)] と K^×/N で一致（差 (0, u) は付値 0 で核 N に属す）。 -/
theorem brf_section_right_inv (U : Grp) (n : Nat) :
    ∀ x, (brfSection U n).map ((brfInv U n).map x) = x := by
  intro x
  induction x using Quot.ind; rename_i a
  show (brfSection U n).map (Quot.mk (modCong n).rel a.1) = Quot.mk _ a
  show (Quot.mk _ ((a.1, U.one) : (unitsModel U).carrier) : (brfQuot U n).carrier)
     = Quot.mk _ a
  apply Quot.sound
  show (kerSubgroup (briInvCyclic U n)).mem
        ((unitsModel U).mul ((unitsModel U).inv (a.1, U.one)) a)
  apply brf_ker_pair
  show ((n : Nat) : Int) ∣ ((unitsModel U).mul ((unitsModel U).inv (a.1, U.one)) a).1
  refine ⟨0, ?_⟩
  show intGrp.mul (intGrp.inv a.1) a.1 = ((n : Nat) : Int) * 0
  rw [Int.mul_zero]
  show (-a.1) + a.1 = 0
  exact Int.add_left_neg a.1

/-! ## M395F-5: 部分群全体での加法性・単射性・像充満 -/

/-- **部分群上で inv は加法的**（M395F-5a）: inv([x]·[y]) = inv([x])+inv([y])。
    巡回代数生成部分群 K^×/N 全体での準同型性（`Hom.map_mul`）。 -/
theorem brf_inv_additive (U : Grp) (n : Nat) (x y : (brfQuot U n).carrier) :
    (brfInv U n).map ((brfQuot U n).mul x y)
      = (briQZn n).mul ((brfInv U n).map x) ((brfInv U n).map y) :=
  (brfInv U n).map_mul x y

/-- **部分群全体で inv は単射**（M395F-5b）: 明示逆 `brfSection` の存在から。
    M365F は単一巡回類上の単射（`bri_inv_injective_cyclic`）だったが、ここでは
    巡回代数生成**部分群全体** K^×/N での単射に締める。 -/
theorem brf_inv_injective_subgroup (U : Grp) (n : Nat) :
    Hom.Injective (brfInv U n) := by
  intro x y h
  calc x = (brfSection U n).map ((brfInv U n).map x) := (brf_section_right_inv U n x).symm
    _ = (brfSection U n).map ((brfInv U n).map y) := by rw [h]
    _ = y := brf_section_right_inv U n y

/-- **像はちょうど (1/n)ℤ/ℤ**（M395F-5c）: 不変量の像が値群全体を尽くす
    （im(inv)=(1/n)ℤ/ℤ）。M365F 全射性の部分群像バージョン。 -/
theorem brf_image_full (U : Grp) (n : Nat) :
    ∀ y : (briQZn n).carrier, (imSubgroup (briInvCyclic U n)).mem y :=
  bri_inv_surjective U n

/-- **inv は全射**（M395F-5d）: K^×/N → (1/n)ℤ/ℤ は全射（切断からも従う）。 -/
theorem brf_inv_surjective (U : Grp) (n : Nat) :
    ∀ y, ∃ x, (brfInv U n).map x = y :=
  fun y => ⟨(brfSection U n).map y, brf_section_left_inv U n y⟩

/-! ## M395F-6: 従順 Hilbert 記号との整合（記号値＝生成する巡回類の不変量） -/

/-- **記号＝生成巡回類の不変量**（M395F-6, 本証明）: 従順 Hilbert 記号（M375F）と
    標準単数 e=(0,1) の対 (a,e)_n は、a の生成する巡回類 [a]∈K^×/N の降下不変量
    inv([a]) に一致する。記号値が「その生成する巡回代数類の不変量」であることを本物で。 -/
theorem brf_tame_symbol_eq_inv (n : Nat) (a : (unitsModel intGrp).carrier) :
    tsyTameSymbol n a ((0 : Int), (1 : Int))
      = (brfInv intGrp n).map
          ((quotientProjN (unitsModel intGrp) (kerSubgroup (briInvCyclic intGrp n))
              (ker_isNormal (briInvCyclic intGrp n))).map a) := by
  rw [tsy_concrete_invariant]
  rfl

/-! ## M395F-7: capstone と n=2 実例 -/

/-- **capstone データ**（M395F-7a）: 巡回代数生成部分群 K^×/N と (1/n)ℤ/ℤ の
    明示同型の全部品 — 降下不変量 inv・明示切断 sec・両側逆律・加法性・単射性・像充満。 -/
structure BrauerInvariantFullData (U : Grp) (n : Nat) where
  /-- 巡回代数生成部分群の模型 K^×/N。 -/
  Sub : Grp
  /-- Sub の同定。 -/
  Sub_is : Sub = brfQuot U n
  /-- 降下不変量 inv: K^×/N → (1/n)ℤ/ℤ。 -/
  inv : Hom (brfQuot U n) (briQZn n)
  /-- inv の同定。 -/
  inv_is : inv = brfInv U n
  /-- 明示切断 sec: (1/n)ℤ/ℤ → K^×/N。 -/
  sec : Hom (briQZn n) (brfQuot U n)
  /-- sec の同定。 -/
  sec_is : sec = brfSection U n
  /-- inv は加法的（部分群上）。 -/
  inv_additive : ∀ x y, (brfInv U n).map ((brfQuot U n).mul x y)
    = (briQZn n).mul ((brfInv U n).map x) ((brfInv U n).map y)
  /-- 左逆律 inv∘sec=id。 -/
  left_inv : ∀ y, (brfInv U n).map ((brfSection U n).map y) = y
  /-- 右逆律 sec∘inv=id。 -/
  right_inv : ∀ x, (brfSection U n).map ((brfInv U n).map x) = x
  /-- inv は部分群全体で単射。 -/
  inv_injective : Hom.Injective (brfInv U n)
  /-- 像はちょうど (1/n)ℤ/ℤ。 -/
  image_full : ∀ y, (imSubgroup (briInvCyclic U n)).mem y

/-- **証人**（M395F-7b）: 全条件を本物の証明で満たす（明示逆付き同型）。 -/
def brfFullData (U : Grp) (n : Nat) : BrauerInvariantFullData U n where
  Sub := brfQuot U n
  Sub_is := rfl
  inv := brfInv U n
  inv_is := rfl
  sec := brfSection U n
  sec_is := rfl
  inv_additive := brf_inv_additive U n
  left_inv := brf_section_left_inv U n
  right_inv := brf_section_right_inv U n
  inv_injective := brf_inv_injective_subgroup U n
  image_full := brf_image_full U n

/-- **巡回代数生成部分群の完全不変量データの存在**（M395F-7c, capstone）。 -/
theorem brf_exists (U : Grp) (n : Nat) : Nonempty (BrauerInvariantFullData U n) :=
  ⟨brfFullData U n⟩

/-- **具体的存在**（M395F-7d）: 自明単数群・n=2 でも明示同型が実体化。 -/
theorem brf_exists_witness : Nonempty (BrauerInvariantFullData punitGrp 2) :=
  ⟨brfFullData punitGrp 2⟩

/-! ## M395F-7e: n=2 実例 — 素元の巡回類の inv=1/2 と従順記号経由の非自明性 -/

/-- **同型の値**（M395F-7e-1, 本証明）: n=2 で inv(sec([1])) = [1]（=1/2）。
    明示逆律の具体化。 -/
theorem brf_two_iso_value (U : Grp) :
    (brfInv U 2).map ((brfSection U 2).map (Quot.mk (modCong 2).rel 1))
      = Quot.mk (modCong 2).rel 1 :=
  brf_section_left_inv U 2 (Quot.mk (modCong 2).rel 1)

/-- **値 1/2 は非自明**（M395F-7e-2, 本証明）: [1]∈(1/2)ℤ/ℤ は ≠0
    （M365F 四元数不変量の再輸出）。同型の像に非零値 1/2 が現れる。 -/
theorem brf_two_value_nontrivial (U : Grp) :
    Quot.mk (modCong 2).rel (1 : Int) ≠ (briQZn 2).one := by
  intro h
  apply bri_quaternion_not_split U
  rw [bri_quaternion_inv]
  exact h

/-- **従順記号経由の非自明類**（M395F-7e-3, 本証明）: 素元 π=(1,0) の生成する
    巡回類 [π]∈K^×/N の降下不変量は ≠0（従順記号 (π,e)_2=1/2 と一致し非自明）。
    巡回代数生成部分群が非自明であることを従順記号経由で実現。 -/
theorem brf_tame_prime_inv_nontrivial :
    (brfInv intGrp 2).map
        ((quotientProjN (unitsModel intGrp) (kerSubgroup (briInvCyclic intGrp 2))
            (ker_isNormal (briInvCyclic intGrp 2))).map ((1 : Int), (0 : Int)))
      ≠ (briQZn 2).one := by
  rw [← brf_tame_symbol_eq_inv 2 ((1 : Int), (0 : Int))]
  exact tsy_example_prime_unit_nontrivial

end IUT
