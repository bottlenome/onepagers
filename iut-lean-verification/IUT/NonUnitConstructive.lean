-- M473F NonUnitConstructive [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M468F(cpd, CoprimalityDecision)が正直に残した限定
--   「gcd(a,n)≠1（互いに素でない）ケースでの非可逆性の証明自体は非構成——
--   `cpdUnitOption` が `none` を返す（witness を構成しない）ことのみを保証し、
--   『a が実際に単元でないことの証明』までは構成しない」を、**gcd(a,n)=g>1 のとき
--   a が (ℤ/n) で本当に非単元であることの構成的証明**（`nuc_non_unit`）へ実際に
--   昇格する。さらに M463F `zib_inverse_correct`（gcd=1 ⟹ 単元）と本モジュールの
--   非単元性を合わせて **`nuc_unit_iff_coprime`**（単元性と互いに素性の完全同値）
--   を証明し、`nuc_exists` で cpd の判定結果と非可逆性の証明を直結する。
--   complete_pct を前進させる昇格作業（(a) 既存モジュールの限定の本物置換）。
-- 正直な限定: 本モジュールが対象とするのは Nat 上の具体的な a, n（単一の有限
--   mod n レベル）の単元性判定のみ——完全副有限 Ẑ^× レベル（無限個の素点に
--   わたる局所的な単元性判定・逆極限との整合）や、決定不能命題一般への拡張は
--   行わない。計算量解析（ユークリッド互除法のステップ数など）も対象外。

/-
  IUT/NonUnitConstructive.lean — M473F [実／昇格・柱E×柱A]

  M468F（CoprimalityDecision, prefix `cpd`）は `cpdCoprime`/`cpd_coprime_correct`
  により gcd(a,n)=1 の判定を decidable 化し、判定が true のときに限り M463F
  `zib_unit_auto` を witness 供給なしで自動起動して `kgcUnitCarrier n` の元を
  構成した（`cpdUnitOption`）。しかし `cpd_model_scope` は次を正直な限定として
  残していた:
    「`cpdUnitOption` が `none` を返すケース（gcd(a,n)≠1）については、a が
     mod n で単元でないことの追加の証明（非可逆性の証明）までは構成しない
     ——witness を構成しないことのみを保証し、構成できないことの証明は別途
     必要であれば別モジュールの課題として正直に残す」

  本モジュールはこの限定を、**gcd(a,n)=g>1 のとき a·y=1（mod n）を満たす
  y が (ℤ/n) 上のどの元にも存在しないことの構成的証明**で実際に閉じる:

  数学的核心: gcd(a,n)=g>1 なら、g∣a かつ g∣n（Nat.gcd の基本性質）。
  任意の整数 y に対し g∣(a·y)（g∣a から）、かつ a·y ≡ 1 (mod n) と仮定すると
  n∣(a·y−1) だから g∣(a·y−1)（g∣n との合成）。g が a·y と a·y−1 を両方
  割り切るなら、その差 1 も割り切る——しかし g>1（実際には g≠1 であれば
  十分）は 1 を割り切らない。矛盾。この整除論法を Nat.gcd の基本性質と
  Int の除法補題のみから完全に構成的に証明する（存在の否定なので選択公理は
  一切不要——witness の非存在を示す普遍量化された矛盾の導出）。

  1. **`nucCommonDivisor`（本丸1）**: g := Nat.gcd a n が a と n の公約数
     であることを Nat.gcd の基本性質から取り出す。
  2. **`nuc_not_dvd_one`（補助・本丸の鍵）**: g≠1 なら (g:Int) は 1 を
     割り切らない。natAbs を経由した Nat への還元で証明する。
  3. **`nuc_mul_divisible`（本丸2）**: gcd(a,n)=g のとき任意の整数 x で
     g ∣ ((a·x) % n)（Int の emod。`Int.dvd_self_sub_emod` と整除の
     引き算則から）。
  4. **`nuc_not_one`（本丸3）**: g>1 のとき、任意の整数 x で
     (a·x) % n ≠ 1（`nuc_mul_divisible` と `nuc_not_dvd_one` の合成）。
  5. **`nuc_non_unit`（本丸4・M468F の限定を閉じる）**: gcd(a,n)>1 なら
     `(zmod n).carrier` のどの元 y についても
     zmodMul n (class a) y ≠ class 1——a が (ℤ/n) で非単元であることを
     **`(zmod n).carrier` 全体にわたって**構成的に証明する（Nat 表現の
     witness だけでなく、Quot.ind による任意代表元での一般証明）。
  6. **`nuc_unit_iff_coprime`（本丸5・完全同値）**: a が (ℤ/n) で単元
     （∃ y, zmodMul n (class a) y = class 1）であることと gcd(a,n)=1 は
     同値。mp 方向は本モジュールの `nuc_non_unit`（gcd≠1 の一般形）、mpr
     方向は M463F `zib_inverse_correct` による。
  7. **`nuc_exists`（capstone・M468F との直結）**: `cpdCoprime a n = false`
     （M468F の判定手続きが「互いに素でない」と判定した場合）なら実際に
     a は (ℤ/n) のどの元によっても単元化できない——M468F が「witness を
     構成しない」ことのみ保証していた false 分岐に、「実際に構成不可能
     であることの証明」を接続する。
  8. `nuc_model_scope`（残る限定の正直な宣言）。

  * M473F-1 `nucCommonDivisor`
  * M473F-2 `nuc_not_dvd_one`
  * M473F-3 `nuc_mul_divisible`
  * M473F-4 `nuc_not_one`
  * M473F-5 `nuc_non_unit_core`/`nuc_non_unit`
  * M473F-6 `nuc_unit_iff_coprime`
  * M473F-7 `nuc_exists`/`nuc_model_scope`

  **正直な限定（消去・弱化禁止）**:
  - 本モジュールが対象とするのは Nat 上の具体的な a, n（単一の有限 mod n
    レベル）の単元性判定のみ——完全副有限 Ẑ^× レベル（無限個の素点にわたる
    局所的な単元性判定・逆極限系との整合性）や、決定不能命題一般への拡張は
    行わない（別経路のまま、本モジュールは統合しない）。
  - 計算量解析（ユークリッド互除法のステップ数、最悪計算量の上界など）は
    引き続き対象外——M468F `cpd_model_scope` の限定 (i) と同様。
  - 全て選択公理不使用（新規 Classical・新規 Classical.choice なし——
    非存在の証明は普遍量化された矛盾の導出であり選択原理を要しない）。
    禁止タクティク不使用（simp/decide/by_cases/rcases/ring/nlinarith/
    positivity/conv/nth_rewrite/field_simp 不使用）。許可タクティクのみ
    （cases/obtain/induction/rw/show/refine/exact/apply/intro/generalize/
    funext/omega、および本コードベースの既存慣行に倣った `rfl`）。
    共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更
    していない。一般名は `nuc` 接頭辞で衝突回避（グレップ確認済み・既存
    コードに重複なし）。
-/
import IUT.CoprimalityDecision

namespace IUT

/-! ## M473F-1: gcd の公約数性 -/

/-- **M473F-1: 本丸・gcd(a,n) は a と n の公約数** — Nat.gcd の基本性質から
    そのまま取り出す。 -/
theorem nucCommonDivisor (a n : Nat) : Nat.gcd a n ∣ a ∧ Nat.gcd a n ∣ n :=
  ⟨Nat.gcd_dvd_left a n, Nat.gcd_dvd_right a n⟩

/-! ## M473F-2: g≠1 は 1 を割り切らない -/

/-- **M473F-2: 補助・本丸の鍵** — g≠1 なら (g:Int) は (1:Int) を割り切らない。
    natAbs を経由して Nat の `Nat.eq_one_of_dvd_one` に還元する。 -/
theorem nuc_not_dvd_one (g : Nat) (hg : g ≠ 1) : ¬ ((g : Nat) : Int) ∣ (1 : Int) := by
  intro h
  have h1 : ((g : Nat) : Int).natAbs ∣ ((1 : Int)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_natCast] at h1
  have h2 : g ∣ 1 := h1
  exact hg (Nat.eq_one_of_dvd_one h2)

/-! ## M473F-3: gcd による割り切れ（emod 版） -/

/-- **M473F-3: 本丸・gcd(a,n) は (a·x) % n を割り切る** — 任意の整数 x で
    g := gcd(a,n) は a·x を割り切り（g∣a から）、a·x と (a·x)%n の差
    （n の倍数、`Int.dvd_self_sub_emod`）も g で割り切れる（g∣n から）ので、
    その差 g∣((a·x) - ((a·x) - (a·x)%n)) = g∣((a·x)%n)。 -/
theorem nuc_mul_divisible (a n : Nat) (x : Int) :
    ((Nat.gcd a n : Nat) : Int) ∣ (((a : Nat) : Int) * x) % ((n : Nat) : Int) := by
  have hga : Nat.gcd a n ∣ a := Nat.gcd_dvd_left a n
  have hgn : Nat.gcd a n ∣ n := Nat.gcd_dvd_right a n
  have hgaI : ((Nat.gcd a n : Nat) : Int) ∣ ((a : Nat) : Int) := Int.ofNat_dvd.mpr hga
  have hgnI : ((Nat.gcd a n : Nat) : Int) ∣ ((n : Nat) : Int) := Int.ofNat_dvd.mpr hgn
  have h1 : ((Nat.gcd a n : Nat) : Int) ∣ ((a : Nat) : Int) * x :=
    Int.dvd_mul_of_dvd_left hgaI
  have h2 : ((Nat.gcd a n : Nat) : Int) ∣
      ((a : Nat) : Int) * x - (((a : Nat) : Int) * x) % ((n : Nat) : Int) :=
    Int.dvd_trans hgnI Int.dvd_self_sub_emod
  have h3 := Int.dvd_sub h1 h2
  generalize hP : ((a : Nat) : Int) * x = P at h3 ⊢
  generalize hQ : P % ((n : Nat) : Int) = Q at h3 ⊢
  have heq : P - (P - Q) = Q := by omega
  rw [heq] at h3
  exact h3

/-! ## M473F-4: g>1 なら a·x ≢ 1 -/

/-- **定理 (M473F-4: 本丸・a·x ≢ 1)** — gcd(a,n)>1 のとき、任意の整数 x で
    (a·x) % n ≠ 1。`nuc_mul_divisible` と `nuc_not_dvd_one` の合成。 -/
theorem nuc_not_one (a n : Nat) (hg : 1 < Nat.gcd a n) (x : Int) :
    (((a : Nat) : Int) * x) % ((n : Nat) : Int) ≠ 1 := by
  intro heq1
  have hdvd := nuc_mul_divisible a n x
  rw [heq1] at hdvd
  exact nuc_not_dvd_one (Nat.gcd a n) (by omega) hdvd

/-! ## M473F-5: 非単元性（M468F の限定を閉じる） -/

/-- **M473F-5a: 内部補助・gcd≠1 一般形の非単元性の核心** — gcd(a,n)≠1 かつ
    n∣(a·x−1) なら矛盾。`nuc_unit_iff_coprime` の mp 方向でも再利用する
    （gcd(a,n)=0 のケース、すなわち a=n=0 も含めて一般に成り立つ：g=0 も
    1 を割り切らないため `nuc_not_dvd_one` がそのまま適用できる）。 -/
theorem nuc_non_unit_core (a n : Nat) (hg : Nat.gcd a n ≠ 1) (x : Int)
    (hdvd : ((n : Nat) : Int) ∣ (((a : Nat) : Int) * x - 1)) : False := by
  have hga : Nat.gcd a n ∣ a := Nat.gcd_dvd_left a n
  have hgn : Nat.gcd a n ∣ n := Nat.gcd_dvd_right a n
  have hgaI : ((Nat.gcd a n : Nat) : Int) ∣ ((a : Nat) : Int) := Int.ofNat_dvd.mpr hga
  have hgnI : ((Nat.gcd a n : Nat) : Int) ∣ ((n : Nat) : Int) := Int.ofNat_dvd.mpr hgn
  have h1 : ((Nat.gcd a n : Nat) : Int) ∣ ((a : Nat) : Int) * x :=
    Int.dvd_mul_of_dvd_left hgaI
  have h2 : ((Nat.gcd a n : Nat) : Int) ∣ ((a : Nat) : Int) * x - 1 :=
    Int.dvd_trans hgnI hdvd
  have h3 := Int.dvd_sub h1 h2
  generalize hP : ((a : Nat) : Int) * x = P at h3
  have heq : P - (P - 1) = 1 := by omega
  rw [heq] at h3
  exact nuc_not_dvd_one (Nat.gcd a n) hg h3

/-- **定理 (M473F-5b: 本丸・M468F の限定を閉じる)** — gcd(a,n)>1 のとき、
    `(zmod n).carrier` の**どの元 y についても** zmodMul n (class a) y は
    class 1 に等しくない。すなわち a は (ℤ/n) で非単元であることを、
    Nat 表現の witness だけでなく**カルリア全体**にわたって（Quot.ind に
    よる任意代表元での証明として）構成的に示す。M468F `cpd_model_scope` が
    「witness を構成しない」ことのみ保証していた非可逆性を、実際の
    非単元性の証明へ昇格する。 -/
theorem nuc_non_unit (a n : Nat) (hg : 1 < Nat.gcd a n) :
    ¬ ∃ y : (zmod n).carrier,
      zmodMul n (Quot.mk (modCong n).rel ((a : Nat) : Int)) y
        = Quot.mk (modCong n).rel (1 : Int) := by
  intro hex
  obtain ⟨y, hy⟩ := hex
  revert hy
  induction y using Quot.ind
  rename_i x
  intro hy
  have hy' : Quot.mk (modCong n).rel (((a : Nat) : Int) * x)
      = Quot.mk (modCong n).rel (1 : Int) := hy
  have hrel := quot_exact intGrp (modCong n) hy'
  exact nuc_non_unit_core a n (by omega) x hrel

/-! ## M473F-6: 単元性と互いに素性の完全同値 -/

/-- **定理 (M473F-6: 本丸・完全同値)** — a が (ℤ/n) で単元
    （∃ y : (zmod n).carrier, zmodMul n (class a) y = class 1）であることと
    gcd(a,n)=1 であることは同値。mp 方向は本モジュール `nuc_non_unit_core`
    （gcd≠1 の一般形、gcd=0 も含む）、mpr 方向は M463F `zib_inverse_correct`
    による自動逆元構成。単元構成（M463F）と非単元性の証明（本モジュール）を
    合わせた IUT ℤ/n^× の完全な特徴づけ。 -/
theorem nuc_unit_iff_coprime (a n : Nat) :
    (∃ y : (zmod n).carrier,
        zmodMul n (Quot.mk (modCong n).rel ((a : Nat) : Int)) y
          = Quot.mk (modCong n).rel (1 : Int))
      ↔ Nat.gcd a n = 1 := by
  constructor
  · intro hex
    obtain ⟨y, hy⟩ := hex
    revert hy
    induction y using Quot.ind
    rename_i x
    intro hy
    have hy' : Quot.mk (modCong n).rel (((a : Nat) : Int) * x)
        = Quot.mk (modCong n).rel (1 : Int) := hy
    have hrel := quot_exact intGrp (modCong n) hy'
    cases hd : Nat.decEq (Nat.gcd a n) 1 with
    | isTrue h => exact h
    | isFalse hne => exact (nuc_non_unit_core a n hne x hrel).elim
  · intro h1
    exact ⟨Quot.mk (modCong n).rel (zibInverse n a), zib_inverse_correct n a h1⟩

/-! ## M473F-7: capstone と残る限定の宣言 -/

/-- **定理 (M473F-7a: capstone・M468F との直結)** — `cpdCoprime a n = false`
    （M468F の判定手続きが「互いに素でない」と判定した場合）なら、
    `(zmod n).carrier` のどの元によっても a は単元化できない。M468F
    `cpdUnitOption` の false 分岐（witness を構成しないことのみ保証）に、
    「実際に構成不可能であることの証明」を接続する。 -/
theorem nuc_exists (a n : Nat) (h : cpdCoprime a n = false) :
    ¬ ∃ y : (zmod n).carrier,
      zmodMul n (Quot.mk (modCong n).rel ((a : Nat) : Int)) y
        = Quot.mk (modCong n).rel (1 : Int) := by
  intro hex
  have heq1 : Nat.gcd a n = 1 := (nuc_unit_iff_coprime a n).mp hex
  have htrue : cpdCoprime a n = true := (cpd_coprime_correct a n).mpr heq1
  rw [htrue] at h
  exact Bool.noConfusion h

/-- **nuc_model_scope（正直な限定の宣言）**: 本モジュールが実際に閉じるのは、
    M468F `cpd_model_scope` が残した「gcd(a,n)≠1 の場合の非可逆性の証明は
    非構成（witness 非構成のみ保証）」という限定であり、`nuc_non_unit`
    （gcd>1 のとき (zmod n).carrier のどの元も a の逆元になり得ないことの
    構成的証明）・`nuc_unit_iff_coprime`（単元性と互いに素性の完全同値）・
    `nuc_exists`（cpd の false 判定と非可逆性の証明の直結）により実際に
    置換する。残る正直な限定は本ファイル冒頭のコメントに明記した通り:
    (i) 対象は Nat 上の具体的な a, n（単一の有限 mod n レベル）のみ——
    完全副有限 Ẑ^× レベルの単元性判定や逆極限系との整合性、決定不能命題
    一般への拡張は行わない、(ii) 判定手続き自体の計算量解析（M468F と同様）
    は対象外。 -/
theorem nuc_model_scope (a n : Nat) (h : cpdCoprime a n = false) :
    ¬ ∃ y : (zmod n).carrier,
      zmodMul n (Quot.mk (modCong n).rel ((a : Nat) : Int)) y
        = Quot.mk (modCong n).rel (1 : Int) :=
  nuc_exists a n h

end IUT
