-- M463F ZmodInverseBezout [実・昇格（(a)）・柱E×柱A]
-- complete_pct 影響: 柱E/柱A で、M458F(kgc, KummerGeneralChar)が正直に残した限定
--   「kgcUnitGroup n の各単元は明示的な逆元データ（ainv）を伴う構成であり、任意の
--   a∈(ℤ/n)^× に対しその逆元をアルゴリズム的に計算する（Bézout の互除法）ことは
--   本モジュールの範囲外——呼び出し側が単元とその明示的逆元のペアを供給する必要が
--   ある」を、**fuel 有界の拡張ユークリッド互除法（zibExtGcd）による逆元の自動計算**
--   （zibInverse・zib_inverse_correct）へ実際に昇格する。gcd(a,n)=1 という一入力
--   仮定のみから witness 供給なしで kgcUnitCarrier n の元を構成する `zib_unit_auto`
--   により、M458F の「呼び出し側供給」の限定を実際に閉じる。complete_pct を前進
--   させる昇格作業（(a) 既存モジュールの限定の本物置換）。
-- 正直な限定: fuel 有界近似（zibExtGcd 自体は fuel 不足では不正確——「常に停止する」
--   ことと「fuel 十分での出力の正しさ」は別命題であり、本モジュールは後者を
--   fuel ≥ m の仮定下でのみ証明する。zibInverse では fuel := a という自明に十分な
--   （a ≤ a）値を選ぶことでこの仮定を自動的に満たす）・gcd(a,n)=1 は引き続き外部
--   仮定（自動判定アルゴリズムなし）・Nat 具体値レベルの逆元計算のみ（Ẑ^× 副有限
--   レベル・ℤ_p 主単数の可逆性 M29 幾何級数法とは別経路、配線しない）。

/-
  IUT/ZmodInverseBezout.lean — M463F [実／昇格・柱E×柱A]

  M458F（KummerGeneralChar, prefix `kgc`）は本物の単元群 `kgcUnitGroup n` を
  「明示的な逆元データを伴う単元の pair」として構成し、`kgc_model_scope` で
  正直に次を限定として残した:
    「kgcUnitGroup n の各要素は自身の逆元を DATA として携える構成であり、任意の
     a∈(ℤ/n)^× に対しその逆元を**アルゴリズム的に計算する**（Bézout の互除法など）
     ことは本モジュールの範囲外——本モジュールを使う側が、単元とその明示的逆元の
     ペアを供給する必要がある。」

  本モジュールはこの限定を、**拡張ユークリッド互除法による逆元の自動計算**で
  実際に閉じる:

  1. **`zibExtGcd`（本丸1・fuel 有界拡張ユークリッド互除法）**: fuel 引数で
     有界化した構造再帰（well-founded recursion を避け、fuel 減少のみで停止性を
     Lean に認識させる）として、Bézout 係数 (g, s, t)（s·m+t·n=g、g=gcd m n）を
     計算する。
  2. **`zib_bezout_correct`（本丸2・拡張ユークリッドの正しさ）**: fuel ≥ m の下で
     zibExtGcd の出力が実際に Nat.gcd m n と Bézout 恒等式を満たすことを、
     fuel についての帰納法（Nat.gcd_rec・Nat.div_add_mod・IUT.Fermat の
     `bezout_step` 結合補題を再利用）で完全証明する。
  3. **`zibInverse`/`zib_inverse_bezout`/`zib_inverse_correct`（本丸3・逆元の
     自動計算とその正しさ）**: fuel := a（常に a ≤ a で十分）で zibExtGcd を
     呼び出し、Bézout の s 係数を mod n 逆元として取り出す。gcd(a,n)=1 の下で
     zmodMul n (class a) (class (zibInverse n a)) = class 1 であることを
     完全証明する——これが M458F の「呼び出し側が逆元を供給する」という限定への
     実際の代替（自動計算）。
  4. **`zib_unit_auto`（本丸4・M458F の限定を閉じる）**: gcd(a,n)=1 という
     一入力仮定のみから、witness（明示的逆元）を呼び出し側が供給することなく
     `kgcUnitCarrier n` の元を構成する。
  5. `zib_exists` — capstone（gcd(a,n)=1 から kgcUnitCarrier n の非空性）。
     `zib_model_scope` — 残る限定の正直な宣言（M458F の限定を実際に閉じたことの
     明示込み）。

  * M463F-1 `zibExtGcd`
  * M463F-2 `zib_bezout_correct`
  * M463F-3 `zibInverse`/`zib_inverse_bezout`/`zib_inverse_correct`
  * M463F-4 `zib_unit_auto`
  * M463F-5 `zib_exists`/`zib_model_scope`
  * M463F-6 実例

  **正直な限定（消去・弱化禁止）**:
  - `zibExtGcd` は fuel 引数による構造再帰として全域定義されており（関数自体は
    任意の入力で必ず停止する——well-founded recursion を経由しない fuel 減少のみに
    よる構造再帰）、その**出力の正しさ**（gcd 一致・Bézout 恒等式）は
    `zib_bezout_correct` により **fuel ≥ m の仮定の下でのみ**証明する。これは
    「真の停止性解析（最小ステップ数の精密な上界）」ではなく、fuel を十分大きく
    （m 自身、あるいはそれ以上に）取ることで正しさを保証する**有界近似**である。
    `zibInverse` はこの仮定を fuel := a（a ≤ a で自明に成立）で自動的に満たす形で
    包んでいるため、`zib_inverse_correct`/`zib_unit_auto` はこの限定を外部から
    意識させない形で閉じている。
  - gcd(a,n) = 1 という前提は本モジュールでも引き続き**外部仮定**（呼び出し側が
    判定・供給する）——素数性判定や gcd=1 の自動証明そのものは本モジュールの範囲外
    （M102F の `IsPrime` 判定・M32 `IsPrime` と同じ位置づけ）。
  - 本モジュールが対象とするのは Nat 上の具体的な a, n（有限 mod n レベル）の
    逆元計算のみ——ℤ_p の主単数の可逆性（M29 `zmod_principal_unit_invertible` の
    幾何級数法、1+pℤ_p の可逆性）や副有限 Ẑ^× レベルの逆元計算へは配線しない
    （別経路のまま、本モジュールは統合しない）。
  - 全て選択公理不使用（新規 Classical・新規 Classical.choice なし）。禁止タクティク
    不使用（simp/decide/by_cases/rcases/ring/nlinarith/positivity/conv/nth_rewrite/
    field_simp 不使用）。許可タクティクのみ（cases/obtain/induction/rw/show/refine/
    exact/apply/intro/generalize/funext/omega）。共有ファイル（IUT.lean・build.sh・
    dashboard.md・graph 系）は一切変更していない。一般名は `zib` 接頭辞で衝突回避
    （グレップ確認済み・既存コードに重複なし）。
-/
import IUT.KummerGeneralChar
import IUT.Fermat

namespace IUT

/-! ## M463F-1: fuel 有界拡張ユークリッド互除法 -/

/-- **M463F-1: 本丸・fuel 有界拡張ユークリッド互除法** — `zibExtGcd fuel m n`
    は (g, s, t) を返す。fuel ≥ m のとき（`zib_bezout_correct` により）
    g = Nat.gcd m n・s·m + t·n = g を満たす。fuel が尽きた場合や m の位置が
    要求と合わない場合は暫定値を返す（fuel 不足時の正しさは主張しない——
    well-founded recursion を避け、fuel の構造再帰のみで全域性を保証する）。 -/
def zibExtGcd : Nat → Nat → Nat → (Nat × Int × Int)
  | 0, m, n =>
    match m with
    | 0 => (n, 0, 1)
    | _ + 1 => (n, 1, 0)
  | fuel + 1, m, n =>
    match m with
    | 0 => (n, 0, 1)
    | m + 1 =>
      ((zibExtGcd fuel (n % (m + 1)) (m + 1)).1,
       (zibExtGcd fuel (n % (m + 1)) (m + 1)).2.2
         - ((n / (m + 1) : Nat) : Int) * (zibExtGcd fuel (n % (m + 1)) (m + 1)).2.1,
       (zibExtGcd fuel (n % (m + 1)) (m + 1)).2.1)

/-! ## M463F-2: 拡張ユークリッドの正しさ -/

/-- **定理 (M463F-2: 本丸・拡張ユークリッドの正しさ)** — fuel ≥ m のとき、
    `zibExtGcd fuel m n` の第一成分は `Nat.gcd m n` に一致し、Bézout 恒等式
    g = m·s + n·t（s,t は第二・第三成分）を満たす。fuel についての帰納法
    （Euclid の再帰 `Nat.gcd_rec`・`Nat.div_add_mod`・`IUT.Fermat.bezout_step`
    の代数的結合補題の再利用）で完全証明する。 -/
theorem zib_bezout_correct : ∀ (fuel m n : Nat), m ≤ fuel →
    (zibExtGcd fuel m n).1 = Nat.gcd m n ∧
    ((zibExtGcd fuel m n).1 : Int)
      = ((m : Nat) : Int) * (zibExtGcd fuel m n).2.1
        + ((n : Nat) : Int) * (zibExtGcd fuel m n).2.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro m n hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    show n = Nat.gcd 0 n ∧
      ((n : Nat) : Int) = ((0 : Nat) : Int) * (0 : Int) + ((n : Nat) : Int) * (1 : Int)
    refine ⟨(Nat.gcd_zero_left n).symm, ?_⟩
    omega
  | succ fuel ih =>
    intro m n hm
    cases m with
    | zero =>
      show n = Nat.gcd 0 n ∧
        ((n : Nat) : Int) = ((0 : Nat) : Int) * (0 : Int) + ((n : Nat) : Int) * (1 : Int)
      refine ⟨(Nat.gcd_zero_left n).symm, ?_⟩
      omega
    | succ m =>
      have hm' : m ≤ fuel := by omega
      have hmodlt : n % (m + 1) < m + 1 := Nat.mod_lt n (by omega)
      have hmodle : n % (m + 1) ≤ fuel := by omega
      obtain ⟨hgeq, hbez⟩ := ih (n % (m + 1)) (m + 1) hmodle
      have hdm : ((m + 1 : Nat) : Int) * ((n / (m + 1) : Nat) : Int)
            + ((n % (m + 1) : Nat) : Int)
          = ((n : Nat) : Int) := by
        have hd := Nat.div_add_mod n (m + 1)
        rw [← Int.natCast_mul, ← Int.natCast_add, hd]
      show (zibExtGcd fuel (n % (m + 1)) (m + 1)).1 = Nat.gcd (m + 1) n ∧
        ((zibExtGcd fuel (n % (m + 1)) (m + 1)).1 : Int)
          = ((m + 1 : Nat) : Int)
              * ((zibExtGcd fuel (n % (m + 1)) (m + 1)).2.2
                  - ((n / (m + 1) : Nat) : Int) * (zibExtGcd fuel (n % (m + 1)) (m + 1)).2.1)
            + ((n : Nat) : Int) * (zibExtGcd fuel (n % (m + 1)) (m + 1)).2.1
      refine ⟨?_, ?_⟩
      · rw [hgeq]
        exact (Nat.gcd_rec (m + 1) n).symm
      · exact bezout_step _ _ _ _ _ _ _ hdm hbez

/-! ## M463F-3: 逆元の自動計算 -/

/-- **M463F-3a: mod n 逆元の自動計算** — fuel := a（`zib_bezout_correct` の
    仮定 a ≤ a を自明に満たす）で `zibExtGcd` を呼び出し、Bézout の s 係数を
    返す。gcd(a,n)=1 のとき、これが実際に a の mod n 逆元になる
    （`zib_inverse_correct`）。 -/
def zibInverse (n a : Nat) : Int :=
  (zibExtGcd a a n).2.1

/-- **定理 (M463F-3b)** — gcd(a,n)=1 のとき 1 = a·zibInverse n a + n·t
    （t = 第二 Bézout 係数）。`zib_bezout_correct` を fuel=a で実インスタンス化。 -/
theorem zib_inverse_bezout (n a : Nat) (h : Nat.gcd a n = 1) :
    (1 : Int) = ((a : Nat) : Int) * zibInverse n a
      + ((n : Nat) : Int) * (zibExtGcd a a n).2.2 := by
  have hc := zib_bezout_correct a a n (Nat.le_refl a)
  have hgeq : (zibExtGcd a a n).1 = 1 := by
    rw [hc.1, h]
  have hbez := hc.2
  rw [hgeq] at hbez
  show (1 : Int) = ((a : Nat) : Int) * (zibExtGcd a a n).2.1
      + ((n : Nat) : Int) * (zibExtGcd a a n).2.2
  have hone : ((1 : Nat) : Int) = 1 := by omega
  rw [hone] at hbez
  exact hbez

/-- **定理 (M463F-3c: 本丸・逆元の自動計算の正しさ)** — gcd(a,n)=1 のとき
    `zibInverse n a` は実際に a の mod n 逆元である:
    zmodMul n (class a) (class (zibInverse n a)) = class 1。**M458F の
    「呼び出し側が逆元 witness を供給する」限定を、自動計算で実際に閉じる本丸。** -/
theorem zib_inverse_correct (n a : Nat) (h : Nat.gcd a n = 1) :
    zmodMul n (Quot.mk (modCong n).rel ((a : Nat) : Int))
        (Quot.mk (modCong n).rel (zibInverse n a))
      = Quot.mk (modCong n).rel 1 := by
  show Quot.mk (modCong n).rel (((a : Nat) : Int) * zibInverse n a)
    = Quot.mk (modCong n).rel 1
  apply Quot.sound
  show ((n : Nat) : Int) ∣ (((a : Nat) : Int) * zibInverse n a - 1)
  have hbez := zib_inverse_bezout n a h
  refine ⟨-(zibExtGcd a a n).2.2, ?_⟩
  rw [Int.mul_neg]
  revert hbez
  generalize ((a : Nat) : Int) * zibInverse n a = X
  generalize ((n : Nat) : Int) * (zibExtGcd a a n).2.2 = Y
  intro hbez
  omega

/-! ## M463F-4: M458F の限定を閉じる — witness なしの単元構成 -/

/-- **定理 (M463F-4: 本丸・M458F の限定を閉じる)** — gcd(a,n)=1 という
    一入力仮定のみから、（M458F が要求していた「明示的逆元 witness の呼び出し側
    供給」なしに）`kgcUnitCarrier n` の元を自動構成する。逆元は `zibInverse`
    による自動計算、正当性は `zib_inverse_correct`。 -/
def zib_unit_auto (n a : Nat) (h : Nat.gcd a n = 1) : kgcUnitCarrier n :=
  ⟨(Quot.mk (modCong n).rel ((a : Nat) : Int), Quot.mk (modCong n).rel (zibInverse n a)),
    zib_inverse_correct n a h⟩

/-! ## M463F-5: capstone と残る限定の宣言 -/

/-- **定理 (M463F-5a: capstone)** — gcd(a,n)=1 なら `kgcUnitCarrier n` は
    非空（witness 供給なしで自動構成した単元による）。 -/
theorem zib_exists (n a : Nat) (h : Nat.gcd a n = 1) : Nonempty (kgcUnitCarrier n) :=
  ⟨zib_unit_auto n a h⟩

/-- **zib_model_scope（正直な限定の宣言）**: 本モジュールが実際に閉じるのは、
    M458F `kgcUnitCarrier n` の構成に必要な「明示的逆元 witness」を、
    gcd(a,n)=1 という一入力仮定から**拡張ユークリッド互除法（zibExtGcd、fuel
    有界構造再帰）で自動計算**し（zibInverse）、それが実際に mod n 逆元である
    ことを証明する（zib_inverse_correct）——これにより M458F kgc_model_scope の
    「呼び出し側が単元とその明示的逆元のペアを供給する必要がある」という限定を、
    witness 自動計算という形で閉じる（zib_unit_auto）。残る正直な限定は本ファイル
    冒頭・各定義のコメントに明記した通り: (i) fuel ≥ m 前提下でのみ出力の正しさを
    証明する有界近似（zibInverse は fuel:=a で自動的に充足）、(ii) gcd(a,n)=1 は
    引き続き外部仮定、(iii) Nat 具体値レベルの逆元計算のみ（Ẑ^× 副有限レベル・
    ℤ_p 主単数可逆性 M29 とは別経路）。 -/
theorem zib_model_scope (n a : Nat) (h : Nat.gcd a n = 1) :
    zmodMul n (Quot.mk (modCong n).rel ((a : Nat) : Int))
        (Quot.mk (modCong n).rel (zibInverse n a))
      = Quot.mk (modCong n).rel 1 :=
  zib_inverse_correct n a h

/-! ## M463F-6: 実例 -/

/-- 実例: a=1 は任意の n と互いに素（`Nat.gcd_one_left`）——`zib_exists` が
    witness 供給なしで単元 (1,1⁻¹) を自動構成し `kgcUnitCarrier 5` が非空で
    あることを示す。 -/
example : Nonempty (kgcUnitCarrier 5) :=
  zib_exists 5 1 (Nat.gcd_one_left 5)

/-- 実例: `zib_bezout_correct` を具体的な小さいケース（fuel=m=2, n=5）に
    実インスタンス化し、拡張ユークリッドの出力が実際に Bézout 恒等式を満たす
    ことを確認する。 -/
example :
    (zibExtGcd 2 2 5).1 = Nat.gcd 2 5 ∧
    ((zibExtGcd 2 2 5).1 : Int)
      = ((2 : Nat) : Int) * (zibExtGcd 2 2 5).2.1 + ((5 : Nat) : Int) * (zibExtGcd 2 2 5).2.2 :=
  zib_bezout_correct 2 2 5 (Nat.le_refl 2)

end IUT
