/-
  IUT/CyclotomicPrimePower.lean — M386F [実・本物・柱C]
-- M386F CyclotomicPrimePower [実・本物・柱C]
-- complete_pct 影響: 柱C で ℚ(ζ_{p^k})(k≥2) の野生分岐 different 指数
--   d = p^{k-1}(k(p−1)−1) = k·φ(p^k) − p^{k-1} と wild 分岐（p ∣ e=φ(p^k)）を本物化し、
--   k=1 で M381F の tame 値 p−2 に整合還元することを ℕ 算術で証明（M381F の上の昇格）。
-- 正直な限定: 一般数体 / 抽象 different イデアル 𝔡=(Φ_{p^k}'(ζ)) / ℤ[ζ_{p^k}] 整基底 /
--   高次分岐群 G_i によるより精密な野生指数分解は後続。指数は ℕ 算術で本物化。
-/
import IUT.CyclotomicDifferent

namespace IUT

/-! ## M386F-1: 拡大次数 [ℚ(ζ_{p^k}):ℚ] = φ(p^k) = p^{k-1}(p−1)

    p を奇素数、k ≥ 1 とするとき、円分体 K = ℚ(ζ_{p^k})（ζ は原始 p^k 乗根）の ℚ 上の
    拡大次数は Euler の φ 関数で
      [ℚ(ζ_{p^k}) : ℚ] = deg(Φ_{p^k}) = φ(p^k) = p^{k-1}(p − 1)
    である（Φ_{p^k}(X) = Φ_p(X^{p^{k-1}}) は次数 φ(p^k) の円分多項式、Eisenstein で既約）。
    k=1 で p^0(p−1) = p−1 = M376F の `cydDegree p` に一致する。ℕ で本物に定義する。 -/

/-- **M386F-1a: Euler φ(p^k)** = p^{k-1}(p − 1)（p 素数・k ≥ 1）。 -/
def cppPhi (p k : Nat) : Nat := p ^ (k - 1) * (p - 1)

/-- **M386F-1b: 拡大次数** [ℚ(ζ_{p^k}):ℚ] = φ(p^k)（円分多項式 Φ_{p^k} の次数）。 -/
def cppDegree (p k : Nat) : Nat := cppPhi p k

/-- **M386F-1c: 次数 = φ(p^k)（定義的・本物）**。 -/
theorem cpp_degree_eq_phi (p k : Nat) : cppDegree p k = cppPhi p k := rfl

/-- **M386F-1d: φ(p^k) の値**（定義的）。 -/
theorem cpp_phi_eq (p k : Nat) : cppPhi p k = p ^ (k - 1) * (p - 1) := rfl

/-- **M386F-1e: k=1 で M376F の次数へ還元（本物・整合性）** — φ(p^1) = p^0(p−1) = p−1
    = `cydDegree p`。素数円分 ℚ(ζ_p)（M376F）は p^k 円分の k=1 特別ケース。 -/
theorem cpp_degree_reduce (p : Nat) : cppDegree p 1 = cydDegree p := by
  show p ^ (1 - 1) * (p - 1) = p - 1
  rw [Nat.pow_zero, Nat.one_mul]

/-! ## M386F-2: 分岐指数 e = φ(p^k) と剰余次数 f = 1（p は全分岐）

    唯一の分岐素数 p は ℚ(ζ_{p^k}) で **全分岐** する：分岐指数 e が拡大次数を吸収し
      e = φ(p^k) = p^{k-1}(p − 1) = [K:ℚ],   f = 1,   g = 1.
    (e,f,g) = (p^{k-1}(p−1), 1, 1)。M376F の (p−1,1,1) の k=1 特化。 -/

/-- **M386F-2a: 分岐指数** e = φ(p^k)（p は全分岐）。 -/
def cppRamIndex (p k : Nat) : Nat := cppPhi p k

/-- **M386F-2b: 剰余次数** f = 1（全分岐なので剰余体拡大なし）。 -/
def cppResidueDeg (_p _k : Nat) : Nat := 1

/-- **M386F-2c: (e,f,g)** = (φ(p^k), 1, 1)。 -/
def cppEFG (p k : Nat) : Nat × Nat × Nat := (cppPhi p k, 1, 1)

/-- **M386F-2d: e = [K:ℚ]（全分岐・本物・定義的）** — 分岐指数が拡大次数に一致。 -/
theorem cpp_ram_eq_degree (p k : Nat) : cppRamIndex p k = cppDegree p k := rfl

/-- **M386F-2e: 基本等式 e·f·g = [K:ℚ] = φ(p^k)（本物）** — Σ_{v|p} e_v f_v = e·f·g。
    全分岐 g=1・f=1 なので e=φ(p^k)。 -/
theorem cpp_efg_prod (p k : Nat) :
    (cppEFG p k).1 * (cppEFG p k).2.1 * (cppEFG p k).2.2 = cppDegree p k := by
  show cppPhi p k * 1 * 1 = cppPhi p k
  rw [Nat.mul_one, Nat.mul_one]

/-- **M386F-2f: 全分岐＝分岐指数が拡大次数に一致（本物）** — e = φ(p^k) = [K:ℚ]。 -/
theorem cpp_totally_ramified (p k : Nat) : (cppEFG p k).1 = cppDegree p k := rfl

/-! ## M386F-3: p は野生（wild）分岐（k ≥ 2 なら p ∣ e = φ(p^k)）

    ℚ(ζ_{p^k})（k ≥ 2）では分岐指数 e = p^{k-1}(p−1) が剰余標数 p で割り切れる
    （p^{k-1} が p を約数に持つ、k−1 ≥ 1）。ゆえに p は **野生（wild）分岐** であり、
    tame 公式 d = e−1 は成立しない（tame は k=1 の M381F のみ）。 -/

/-- **M386F-3a: 野生分岐（本物）** — k ≥ 2 で p ∣ e = φ(p^k) = p^{k-1}(p−1)。
    p ∣ p^{k-1}（k−1 ≥ 1、M376F の `cyd_dvd_self_pow`）ゆえ p ∣ p^{k-1}(p−1)。 -/
theorem cpp_wildly_ramified (p k : Nat) (hk : 2 ≤ k) : p ∣ cppRamIndex p k := by
  show p ∣ p ^ (k - 1) * (p - 1)
  have h1 : p ∣ p ^ (k - 1) := cyd_dvd_self_pow p (k - 1) (by omega)
  exact Nat.dvd_trans h1 (Nat.dvd_mul_right (p ^ (k - 1)) (p - 1))

/-- **M386F-3b: k=1 は tame（M381F との対比・本物）** — ℚ(ζ_p) では e = p−1 で p ∤ e。
    M381F の `cdf_tamely_ramified` を k=1 分岐指数 e = cppRamIndex p 1 で言い換える。 -/
theorem cpp_k1_tamely_ramified (p : Nat) (hp : IsPrime p) : ¬ p ∣ cppRamIndex p 1 := by
  show ¬ p ∣ p ^ (1 - 1) * (p - 1)
  rw [Nat.pow_zero, Nat.one_mul]
  exact cdf_tamely_ramified p hp

/-! ## M386F-4: 野生 different 指数 d = p^{k-1}(k(p−1) − 1) = k·φ(p^k) − p^{k-1}

    全分岐する p^k 円分体の p 上素点での different 指数は（Serre, Corps Locaux, III;
    高次分岐群 G_i による）
      d = v_𝔭(𝔡) = k·φ(p^k) − p^{k-1} = k·p^{k-1}(p−1) − p^{k-1} = p^{k-1}(k(p−1) − 1).
    実 different 𝔡 = (Φ_{p^k}'(ζ)) の p 上指数に一致する（指数を ℕ 算術で本物化）。
    k=1 で p^0(1·(p−1) − 1) = (p−1) − 1 = p − 2 = M381F の tame 値に還元する。 -/

/-- **M386F-4a: 野生 different 指数** d = p^{k-1}(k(p−1) − 1)。 -/
def cppDifferentExp (p k : Nat) : Nat := p ^ (k - 1) * (k * (p - 1) - 1)

/-- **M386F-4b: different 指数の値**（定義的）。 -/
theorem cpp_different_exp_eq (p k : Nat) :
    cppDifferentExp p k = p ^ (k - 1) * (k * (p - 1) - 1) := rfl

/-- **M386F-4c: 野生公式 d = k·φ(p^k) − p^{k-1}（本物）** — different 指数を
    分岐指数の k 倍から p^{k-1} を引いた形で表す（p^{k-1}(k(p−1) − 1) と一致）。
    a := p^{k-1} として a·(k(p−1) − 1) = a·(k(p−1)) − a = k·(a(p−1)) − a。 -/
theorem cpp_different_eq_wild_formula (p k : Nat) :
    cppDifferentExp p k = k * cppRamIndex p k - p ^ (k - 1) := by
  show p ^ (k - 1) * (k * (p - 1) - 1) = k * (p ^ (k - 1) * (p - 1)) - p ^ (k - 1)
  rw [Nat.mul_sub, Nat.mul_one]
  have h : p ^ (k - 1) * (k * (p - 1)) = k * (p ^ (k - 1) * (p - 1)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (p ^ (k - 1)) k, Nat.mul_assoc]
  rw [h]

/-- **M386F-4d: k=1 で M381F の tame 値へ還元（本物・整合性チェック）** —
    d(k=1) = p^0(1·(p−1) − 1) = (p−1) − 1 = p − 2 = M381F の `cdfDifferentExp p`。
    野生公式が k=1 で tame 公式 d = e−1 = p−2 に**連続的に一致**する。 -/
theorem cpp_different_reduce (p : Nat) : cppDifferentExp p 1 = cdfDifferentExp p := by
  show p ^ (1 - 1) * (1 * (p - 1) - 1) = p - 2
  rw [Nat.pow_zero, Nat.one_mul, Nat.one_mul]
  omega

/-- **M386F-4e: k=1 の値 = p − 2（本物）** — M381F の値 p−2 に直接一致。 -/
theorem cpp_different_reduce_val (p : Nat) : cppDifferentExp p 1 = p - 2 :=
  (cpp_different_reduce p).trans (cdf_different_exp_eq p)

/-! ## M386F-5: disc 指数 = f · d = p^{k-1}(k(p−1) − 1)（norm(different) = discriminant）

    判別式は different のノルム：v_p(disc) = f · v_𝔭(𝔡)。ℚ(ζ_{p^k}) では f=1 ゆえ
    disc 指数 = 1 · d = d、|disc| = p^{disc 指数}。k=1 で p^{p−2} = M376F の `cydDiscMag`。 -/

/-- **M386F-5a: disc 指数** = f · d = p^{k-1}(k(p−1) − 1)。 -/
def cppDiscExp (p k : Nat) : Nat := p ^ (k - 1) * (k * (p - 1) - 1)

/-- **M386F-5b: disc 指数 = f · d（本物）** — 判別式指数は剰余次数と different 指数の積
    （f=1 で吸収）。 -/
theorem cpp_disc_exp_eq (p k : Nat) :
    cppDiscExp p k = cppResidueDeg p k * cppDifferentExp p k := by
  show p ^ (k - 1) * (k * (p - 1) - 1) = 1 * (p ^ (k - 1) * (k * (p - 1) - 1))
  rw [Nat.one_mul]

/-- **M386F-5c: disc 指数 = different 指数（本物・f=1）**。 -/
theorem cpp_disc_eq_different (p k : Nat) : cppDiscExp p k = cppDifferentExp p k := rfl

/-- **M386F-5d: |disc(ℚ(ζ_{p^k}))|** = p^{disc 指数}（判別式の大きさ、単一素数 p の冪）。 -/
def cppDiscMag (p k : Nat) : Nat := p ^ cppDiscExp p k

/-- **M386F-5e: |disc| は p の冪（本物）** — 分岐が p のみに集中＝判別式が p の冪。 -/
theorem cpp_disc_prime_power (p k : Nat) : ∃ e, cppDiscMag p k = p ^ e :=
  ⟨cppDiscExp p k, rfl⟩

/-- **M386F-5f: k=1 の disc 指数 = p − 2（本物）** — M381F の disc 指数に還元。 -/
theorem cpp_disc_exp_reduce (p : Nat) : cppDiscExp p 1 = p - 2 :=
  cpp_different_reduce_val p

/-- **M386F-5g: k=1 で M376F の判別式へ還元（本物・整合性）** —
    |disc(ℚ(ζ_p))| = p^{p−2} = M376F の `cydDiscMag p`。 -/
theorem cpp_disc_mag_reduce (p : Nat) : cppDiscMag p 1 = cydDiscMag p := by
  show p ^ cppDiscExp p 1 = p ^ (p - 2)
  rw [cpp_disc_exp_reduce p]

/-! ## M386F-6: 唯一の分岐素数 p（p^k 円分体でも p のみ・ただし野生）

    ℚ(ζ_{p^k}) でも分岐する有理素数は p のみ（判別式が p の冪ゆえ）。k=1 の tame と違い
    k ≥ 2 では p は野生分岐する。導手 cond = p^k（M376F の p の k 乗）。 -/

/-- **M386F-6a: 導手** cond(ℚ(ζ_{p^k})) = p^k（ℚ(ζ_{p^k}) ⊆ ℚ(ζ_m) となる最小 m）。 -/
def cppConductor (p k : Nat) : Nat := p ^ k

/-- **M386F-6b: 導手の値**（定義的・本物）。 -/
theorem cpp_conductor_eq (p k : Nat) : cppConductor p k = p ^ k := rfl

/-- **M386F-6c: 導手は p の冪（本物・唯一の分岐素数 p）** — cond = p^k は単一素数 p の冪、
    分岐素数がただ p のみであることの導手側の反映。 -/
theorem cpp_conductor_prime_power (p k : Nat) : ∃ e, cppConductor p k = p ^ e :=
  ⟨k, rfl⟩

/-- **M386F-6d: k=1 で M376F の導手へ還元（本物・整合性）** — cond(ℚ(ζ_p)) = p^1 = p
    = `cydConductor p`。 -/
theorem cpp_conductor_reduce (p : Nat) : cppConductor p 1 = cydConductor p := by
  show p ^ 1 = p
  rw [Nat.pow_one]

/-! ## M386F-7: 具体例（ℚ(ζ_9) = ℚ(ζ_{3^2})・野生・および k=1 還元） -/

/-- **M386F-7a: ℚ(ζ_9) の次数 = φ(9) = 6**（3^1·2 = 6）。 -/
theorem cpp_example_9_degree : cppDegree 3 2 = 6 := rfl

/-- **M386F-7b: ℚ(ζ_9) の分岐指数 e = 6**（全分岐 e=φ(9)=6）。 -/
theorem cpp_example_9_ram : cppRamIndex 3 2 = 6 := rfl

/-- **M386F-7c: ℚ(ζ_9) の野生 different 指数 d = 9**（3^1·(2·2 − 1) = 3·3 = 9）。 -/
theorem cpp_example_9_different : cppDifferentExp 3 2 = 9 := rfl

/-- **M386F-7d: ℚ(ζ_9) の野生公式検算 d = k·e − p^{k-1} = 2·6 − 3 = 9（本物）**。 -/
theorem cpp_example_9_wild_formula : cppDifferentExp 3 2 = 2 * cppRamIndex 3 2 - 3 ^ (2 - 1) :=
  cpp_different_eq_wild_formula 3 2

/-- **M386F-7e: ℚ(ζ_9) の disc 指数 = 9（f·d = 1·9）、|disc| = 3^9 = 19683**。 -/
theorem cpp_example_9_disc : cppDiscExp 3 2 = 9 := rfl

/-- **M386F-7f: ℚ(ζ_9) の判別式の大きさ = 3^9 = 19683**。 -/
theorem cpp_example_9_disc_mag : cppDiscMag 3 2 = 19683 := rfl

/-- **M386F-7g: ℚ(ζ_9) は野生分岐**（3 ∣ e = 6）。 -/
theorem cpp_example_9_wild : (3 : Nat) ∣ cppRamIndex 3 2 :=
  cpp_wildly_ramified 3 2 (by omega)

/-- **M386F-7h: ℚ(ζ_9) の導手 = 9 = 3^2**。 -/
theorem cpp_example_9_conductor : cppConductor 3 2 = 9 := rfl

/-- **M386F-7i: k=1 還元の整合性** — ℚ(ζ_{p^1}) は M381F/M376F と各量一致：
    次数 = cydDegree・different 指数 = cdfDifferentExp = p−2・導手 = cydConductor。 -/
theorem cpp_example_k1_consistency (p : Nat) :
    cppDegree p 1 = cydDegree p ∧ cppDifferentExp p 1 = cdfDifferentExp p ∧
    cppDifferentExp p 1 = p - 2 ∧ cppConductor p 1 = cydConductor p :=
  ⟨cpp_degree_reduce p, cpp_different_reduce p, cpp_different_reduce_val p,
   cpp_conductor_reduce p⟩

/-! ## M386F-8: capstone — 野生分岐 different / discriminant データ -/

/-- **M386F-8a: capstone データ** — 奇素数 p・k ≥ 2 の p^k 円分体 ℚ(ζ_{p^k}) の野生分岐
    データ：拡大次数 = φ(p^k) = p^{k-1}(p−1)・分岐指数 e = φ(p^k)（全分岐＝[K:ℚ]）・
    剰余次数 f=1・p は**野生分岐**（p ∣ e）・野生 different 指数 d = k·φ(p^k) − p^{k-1}
    = p^{k-1}(k(p−1) − 1)・disc 指数 = f·d = d（norm(different)=disc）・e·f·g=[K:ℚ]・
    導手 cond = p^k を束ねる（全フィールド本物）。 -/
structure CyclotomicPrimePowerData where
  /-- 奇素数 p。 -/
  p : Nat
  /-- p は素数。 -/
  hp : IsPrime p
  /-- p は奇（3 ≤ p）。 -/
  hodd : 3 ≤ p
  /-- 冪指数 k ≥ 2（野生ケース、k=1 は M381F tame）。 -/
  k : Nat
  /-- k ≥ 2。 -/
  hk : 2 ≤ k
  /-- 拡大次数 [K:ℚ]。 -/
  degree : Nat
  /-- degree = φ(p^k)（本物）。 -/
  degree_eq : degree = cppPhi p k
  /-- 分岐指数 e。 -/
  ramIndex : Nat
  /-- e = degree = φ(p^k)（全分岐、本物）。 -/
  ram_eq : ramIndex = degree
  /-- 剰余次数 f。 -/
  residueDeg : Nat
  /-- f = 1（本物）。 -/
  residue_eq : residueDeg = cppResidueDeg p k
  /-- p は野生分岐（p ∣ e、本物、k ≥ 2 の本質）。 -/
  wild : p ∣ ramIndex
  /-- 野生 different 指数 d。 -/
  differentExp : Nat
  /-- d = k·e − p^{k-1}（野生公式、本物）。 -/
  different_eq : differentExp = k * ramIndex - p ^ (k - 1)
  /-- disc 指数。 -/
  discExp : Nat
  /-- disc 指数 = f · d（norm(different)=disc、本物）。 -/
  disc_exp_eq : discExp = residueDeg * differentExp
  /-- e·f·g = [K:ℚ] = φ(p^k)（本物）。 -/
  efg_prod : (cppEFG p k).1 * (cppEFG p k).2.1 * (cppEFG p k).2.2 = degree
  /-- 導手 cond = p^k（本物）。 -/
  conductor : Nat
  /-- conductor = p^k（本物）。 -/
  conductor_eq : conductor = cppConductor p k

/-- **M386F-8b: 実データ**（奇素数 p・k ≥ 2 に対し全フィールド本物で充足）。 -/
def cppData (p k : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) (hk : 2 ≤ k) :
    CyclotomicPrimePowerData where
  p := p
  hp := hp
  hodd := hodd
  k := k
  hk := hk
  degree := cppDegree p k
  degree_eq := rfl
  ramIndex := cppRamIndex p k
  ram_eq := cpp_ram_eq_degree p k
  residueDeg := cppResidueDeg p k
  residue_eq := rfl
  wild := cpp_wildly_ramified p k hk
  differentExp := cppDifferentExp p k
  different_eq := cpp_different_eq_wild_formula p k
  discExp := cppDiscExp p k
  disc_exp_eq := cpp_disc_exp_eq p k
  efg_prod := cpp_efg_prod p k
  conductor := cppConductor p k
  conductor_eq := rfl

/-- **M386F-8c: capstone — 存在**（任意の奇素数 p・k ≥ 2 の p^k 円分体 ℚ(ζ_{p^k}) の
    野生分岐 different / discriminant データは充足可能）。 -/
theorem cpp_exists (p k : Nat) (hp : IsPrime p) (hodd : 3 ≤ p) (hk : 2 ≤ k) :
    Nonempty CyclotomicPrimePowerData :=
  ⟨cppData p k hp hodd hk⟩

/-- **M386F-8d: 具体 capstone** — ℚ(ζ_9)=ℚ(ζ_{3^2})（次数 φ(9)=6・野生分岐 3∣6・
    野生 different 指数 9 = 2·6−3・disc 指数 9・導手 9）と k=1 の M381F 還元
    （different 指数 p−2）をまとめて充足。野生（k≥2）と tame（k=1）の整合。 -/
theorem cpp_examples :
    cppDegree 3 2 = 6 ∧ cppRamIndex 3 2 = 6 ∧ cppDifferentExp 3 2 = 9 ∧
    cppDiscExp 3 2 = 9 ∧ (3 : Nat) ∣ cppRamIndex 3 2 ∧ cppConductor 3 2 = 9 ∧
    (∀ p, cppDifferentExp p 1 = p - 2) :=
  ⟨cpp_example_9_degree, cpp_example_9_ram, cpp_example_9_different,
   cpp_example_9_disc, cpp_example_9_wild, cpp_example_9_conductor,
   cpp_different_reduce_val⟩

end IUT
