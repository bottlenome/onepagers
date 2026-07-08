-- M468F CoprimalityDecision [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M463F(zib, ZmodInverseBezout)が正直に残した限定
--   「gcd(a,n)=1 という前提は本モジュールでも引き続き外部仮定（呼び出し側が判定・
--   供給する）——自動 coprimality 判定手続きなし」を、**Nat.gcd の計算結果と
--   `1` との decidable な等価判定（cpdCoprime）**へ実際に昇格する。判定が
--   true のときに限り M463F `zib_unit_auto` を witness なしで自動起動して
--   `kgcUnitCarrier n` の元を構成し（`cpdUnitOption`）、判定が false のときは
--   構成を拒否する（`none`）——「gcd=1 は外部仮説」という限定を、判定手続きへ
--   実際に置換する。complete_pct を前進させる昇格作業（(a) 既存モジュールの
--   限定の本物置換）。
-- 正直な限定: 判定は Nat.gcd（具体の Nat 値レベル）の**計算**に依存し、計算量
--   （ユークリッド互除法のステップ数）についての解析は行わない・完全副有限
--   Ẑ^× レベルの互いに素判定（無限個の素点にわたる判定）は本モジュールの範囲外・
--   決定不能命題や無限判定への一般化はしない。

/-
  IUT/CoprimalityDecision.lean — M468F [実／昇格・柱E×柱A]

  M463F（ZmodInverseBezout, prefix `zib`）は `zibInverse`/`zib_unit_auto` により
  「明示的逆元 witness の呼び出し側供給」という M458F の限定を、拡張ユークリッド
  互除法による逆元の自動計算へ昇格した。しかし `zib_model_scope` は次を
  正直な限定として残していた:
    「gcd(a,n) = 1 という前提は本モジュールでも引き続き**外部仮定**（呼び出し側が
     判定・供給する）——素数性判定や gcd=1 の自動証明そのものは本モジュールの
     範囲外」

  本モジュールはこの限定を、**decidable な互いに素判定手続き**で実際に閉じる:

  1. **`cpdCoprime`（本丸1・decidable な互いに素判定）**: `Nat.gcd a n` を計算し、
     それが `1` と等しいかを `Nat.decEq`（Nat 上の既存 DecidableEq、`decide`
     タクティクは不使用）による場合分けで Bool へ落とす。
  2. **`cpd_coprime_correct`（本丸2・判定の正しさ）**: `cpdCoprime a n = true ↔
     Nat.gcd a n = 1` を、判定の定義に用いた `Nat.decEq` の場合分けそのものから
     完全証明する——判定結果と実際の互いに素性が一致することの保証。
  3. **`cpdUnitOption`（本丸3・判定結果からの自動構成）**: `cpdCoprime` が
     true の場合に限り M463F `zib_unit_auto` を（判定が供給する gcd=1 の証拠
     から）witness なしで自動起動し `kgcUnitCarrier n` の元を構成する。false の
     場合は `none`（単元を構成しない）。
  4. **`cpd_unit_some_iff`（本丸4・判定と構成の整合）**: `(cpdUnitOption n a).isSome
     = true ↔ Nat.gcd a n = 1`——判定手続きと単元構成が完全に整合することを
     証明する。
  5. **`cpd_decidable`（本丸5・M463F の外部仮説を判定手続きへ）**: `Nat.gcd a n = 1`
     が実際に decidable（`Nat.decEq` によるインスタンス）であることを明示し、
     M463F `zib_model_scope` の「gcd=1 は外部仮説」を「gcd=1 は本モジュールの
     判定手続きで自動的に決定可能」へ置き換えたことを示す。
  6. `cpd_example_coprime`/`cpd_example_not` — 具体例（gcd(3,7)=1 で単元自動構成・
     gcd(2,4)=2≠1 で構成拒否）。
  7. `cpd_exists`（capstone）・`cpd_model_scope`（残る限定の正直な宣言）。

  * M468F-1 `cpdCoprime`
  * M468F-2 `cpd_coprime_correct`
  * M468F-3 `cpdUnitOption`
  * M468F-4 `cpd_unit_some_iff`
  * M468F-5 `cpd_decidable`
  * M468F-6 `cpd_example_coprime`/`cpd_example_not`
  * M468F-7 `cpd_exists`/`cpd_model_scope`

  **正直な限定（消去・弱化禁止）**:
  - `cpdCoprime`/`cpd_decidable` は `Nat.gcd a n` を実際に**計算**して `1` と
    比較する判定であり、その計算量（ユークリッド互除法のステップ数の解析、
    最悪計算量の上界など）は本モジュールの対象外——判定が「有限時間で停止し
    正しい結果を返す」ことのみを保証する（Nat.gcd 自体は core の well-founded
    構造再帰で全域性が保証済み・fuel 概念は不要——M463F `zibExtGcd` の fuel
    有界近似とは別レイヤー）。
  - 本モジュールが対象とするのは Nat 上の具体的な a, n（有限 mod n レベル）の
    互いに素判定のみ——完全副有限 Ẑ^× レベル（無限個の素点にわたる局所的な
    互いに素性判定）や、決定不能な命題一般への拡張は行わない（別経路のまま、
    本モジュールは統合しない）。
  - `cpdUnitOption` が `none` を返すケース（gcd(a,n)≠1）については、`a` が
    mod n で単元でないことの**追加の証明**（非可逆性の証明）までは構成しない
    ——「witness を構成しない」ことのみを保証し、「構成できないことの証明」は
    別途必要であれば別モジュールの課題として正直に残す。
  - 全て選択公理不使用（新規 Classical・新規 Classical.choice なし）。禁止タクティク
    不使用（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
    field_simp 不使用——`decide` **タクティク**は一切使わず、`Nat.decEq` という
    既存の decidability インスタンス項の場合分けのみで判定を構成・証明する）。
    許可タクティクのみ（cases/obtain/induction/rw/show/refine/exact/apply/intro/
    generalize/funext/omega、および本コードベースの既存慣行に倣った `rfl`）。
    共有ファイル（IUT.lean・build.sh・dashboard.md・graph 系）は一切変更していない。
    一般名は `cpd` 接頭辞で衝突回避（グレップ確認済み・既存コードに重複なし）。
-/
import IUT.ZmodInverseBezout

namespace IUT

/-! ## M468F-1: decidable な互いに素判定 -/

/-- **M468F-1: 本丸・decidable な互いに素判定** — `cpdCoprime a n` は
    `Nat.gcd a n = 1` を Bool で判定する。判定は `Nat.decEq`（Nat の既存
    DecidableEq インスタンス、`decide` タクティクは不使用）による場合分けで
    構成する。M463F の「gcd(a,n)=1 は外部仮説」をここで判定手続きへ置換する。 -/
def cpdCoprime (a n : Nat) : Bool :=
  match Nat.decEq (Nat.gcd a n) 1 with
  | isTrue _ => true
  | isFalse _ => false

/-! ## M468F-2: 判定の正しさ -/

/-- **定理 (M468F-2: 本丸・判定の正しさ)** — `cpdCoprime a n = true` であることと
    `Nat.gcd a n = 1` であることは同値。判定の定義に用いた `Nat.decEq` の
    場合分けそのものから完全証明する。 -/
theorem cpd_coprime_correct (a n : Nat) :
    cpdCoprime a n = true ↔ Nat.gcd a n = 1 := by
  show (match Nat.decEq (Nat.gcd a n) 1 with
      | isTrue _ => true
      | isFalse _ => false) = true ↔ Nat.gcd a n = 1
  cases Nat.decEq (Nat.gcd a n) 1 with
  | isTrue h => exact ⟨fun _ => h, fun _ => rfl⟩
  | isFalse h => exact ⟨fun hc => Bool.noConfusion hc, fun hc => absurd hc h⟩

/-! ## M468F-3: 判定結果からの自動構成 -/

/-- **M468F-3: 本丸・判定結果からの単元自動構成** — `cpdCoprime` が true の
    場合に限り、判定が供給する gcd=1 の証拠から M463F `zib_unit_auto` を
    witness なしで自動起動し `kgcUnitCarrier n` の元を構成する。false の
    場合は構成を拒否する（`none`）。 -/
def cpdUnitOption (n a : Nat) : Option (kgcUnitCarrier n) :=
  match Nat.decEq (Nat.gcd a n) 1 with
  | isTrue h => some (zib_unit_auto n a h)
  | isFalse _ => none

/-! ## M468F-4: 判定と構成の整合 -/

/-- **定理 (M468F-4: 本丸・判定と単元構成の整合)** — `cpdUnitOption n a` が
    `some` を返すこと（`isSome`）と `Nat.gcd a n = 1` であることは同値。 -/
theorem cpd_unit_some_iff (n a : Nat) :
    (cpdUnitOption n a).isSome = true ↔ Nat.gcd a n = 1 := by
  show (match Nat.decEq (Nat.gcd a n) 1 with
      | isTrue h => some (zib_unit_auto n a h)
      | isFalse _ => (none : Option (kgcUnitCarrier n))).isSome = true
    ↔ Nat.gcd a n = 1
  cases Nat.decEq (Nat.gcd a n) 1 with
  | isTrue h => exact ⟨fun _ => h, fun _ => rfl⟩
  | isFalse h => exact ⟨fun hc => Bool.noConfusion hc, fun hc => absurd hc h⟩

/-! ## M468F-5: M463F の外部仮説を判定手続きへ -/

/-- **定理 (M468F-5: 本丸・M463F の外部仮説を判定手続きへ)** — `Nat.gcd a n = 1`
    は実際に decidable（`Nat.decEq` による既存インスタンス）であることを明示する。
    これにより M463F `zib_model_scope` が残した「gcd(a,n)=1 は外部仮説（自動
    coprimality 判定手続きなし）」という限定を、「gcd=1 は本モジュールの判定
    手続き（`cpdCoprime`／`cpd_coprime_correct`）で自動的に決定可能」へ実際に
    置換したことを示す。 -/
def cpd_decidable (a n : Nat) : Decidable (Nat.gcd a n = 1) :=
  Nat.decEq (Nat.gcd a n) 1

/-! ## M468F-6: 実例 -/

/-- 実例: gcd(3,7)=1（互いに素）——判定手続きが true を返し、witness 供給
    なしで `kgcUnitCarrier 7` の元が自動構成される（`isSome`）。 -/
theorem cpd_example_coprime : (cpdUnitOption 7 3).isSome = true :=
  (cpd_unit_some_iff 7 3).mpr rfl

/-- 実例: gcd(2,4)=2≠1（互いに素でない）——判定手続きが false を返し、
    単元の構成が拒否される（`none`）。 -/
theorem cpd_example_not : cpdUnitOption 4 2 = none := by
  show (match Nat.decEq (Nat.gcd 2 4) 1 with
      | isTrue h => some (zib_unit_auto 4 2 h)
      | isFalse _ => (none : Option (kgcUnitCarrier 4)))
    = none
  cases hd : Nat.decEq (Nat.gcd 2 4) 1 with
  | isTrue h =>
    exact absurd h (by
      have hg : Nat.gcd 2 4 = 2 := rfl
      rw [hg]
      omega)
  | isFalse h => rfl

/-! ## M468F-7: capstone と残る限定の宣言 -/

/-- **定理 (M468F-7a: capstone)** — `cpdCoprime a n = true` ならば
    `kgcUnitCarrier n` は非空（判定手続きが自動供給する gcd=1 の証拠から
    M463F `zib_exists` を経由）。 -/
theorem cpd_exists (n a : Nat) (h : cpdCoprime a n = true) :
    Nonempty (kgcUnitCarrier n) :=
  zib_exists n a ((cpd_coprime_correct a n).mp h)

/-- **cpd_model_scope（正直な限定の宣言）**: 本モジュールが実際に閉じるのは、
    M463F `zib_model_scope` が残した「gcd(a,n)=1 は外部仮説（自動 coprimality
    判定手続きなし）」という限定であり、`cpdCoprime`（`Nat.gcd` の計算と `1`
    との `Nat.decEq` 判定）・`cpd_coprime_correct`（判定の正しさ）・
    `cpdUnitOption`（判定結果からの witness 供給なしの自動単元構成）により、
    gcd=1 の判定から単元構成までを外部仮説なしで自動化する。残る正直な限定は
    本ファイル冒頭のコメントに明記した通り: (i) 判定は Nat 具体値レベルの
    計算（計算量解析は対象外）、(ii) 完全副有限 Ẑ^× レベルの判定・決定不能
    命題一般への拡張は行わない、(iii) `none`（互いに素でない）の場合の
    「非可逆性の証明」自体は構成しない（witness 非構成のみを保証）。 -/
theorem cpd_model_scope (n a : Nat) (h : cpdCoprime a n = true) :
    Nonempty (kgcUnitCarrier n) :=
  cpd_exists n a h

end IUT
