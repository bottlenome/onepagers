# 独立再監査 — A2（実 p 進局所体 K_v）2026-07-10

監査者: 独立・敵対的監査（opus・自己申告非共有・実 Lean 定義のみを精読し自走検証）
対象: 柱 A2「実 p 進局所体 K_v(完備化)を実際の対象として構成」（weight 8）
前回: status 0.5（付値機構は本物だが complete_note が「実 p 進局所体 K_v も皆無」）
今回の主張: 実 ℤ₃ 付値環 + 𝔽₃ + 完備性 + 実 ℚ₃ 体 + ℚ₃^× の新規一式で 0.5→0.65

## 判定: **A2 = 0.65**（設計上限どおり・過大主張なし）。柱A% 45 → **46**（+1）。

---

## 0. 自走検証の証跡（自己申告を信用せず自分で走らせた）

- `export PATH="/root/lean4/bin:$PATH" && bash build.sh` → **EXIT=0・no sorry**（build.sh 末尾
  "OK: all theorems verified, no sorry."）。grep で A2 5 ファイルに sorry/admit 皆無を確認
  （ヒットは header の「sorry 皆無」コメントのみ）。
- **独立 #print axioms（build.sh の印字に頼らず自分で列挙）**: A2 5 ファイル
  （Zp3ValuationRing / F3Field / Zp3Complete / Q3LocalField / Q3UnitsGroup）の
  **全 public 対象 70 個を grep 抽出 → `lake env lean` で #print axioms を一括実行**
  （scratchpad/a2_axioms.lean・EXIT=0）。結果: **全 70 対象が [propext, Quot.sound] 以下**
  （z3cModUp/q3_ringLocPow_eq_rpow/z3vRingEquivData は公理なし、z3cModUp_ge/mono/step は [propext]、
  残りは [propext, Quot.sound]）。**新規 Classical.choice は 1 個も無い**。核心対象
  q3f_has_inverses・z3c_val_compat・z3v_extract・z3vMaximal・z3v_res_iso・f3Field・
  q3f_uniformizer・q3u_embed_inj・q3u_image_char すべて [propext, Quot.sound]。

## 1. ℚ₃ が本物の体オブジェクトか（最重要・模型でないか）— YES

- `q3Ring := ringLocRf z3 q3fThree` で `z3 := zpRing 3`・`q3fThree := z3vP 3 = (toZp 3).map 3`。
- `zpRing 3` の担体は `(Zp 3).carrier`、`Zp 3 := limitGrp (padicSystem 3)` = **本物の逆極限
  ℤ₃ = lim ℤ/3ⁿ**（Ring.lean:178-193 / LocalCFT.lean:90）。模型でない。
- `ringLocRf R f := ringLocRing R (ringLocPowers R f)`、`ringLocRel S x y := ∃t∈S,
  t·(x.num·y.den)=t·(y.num·x.den)`（RingLocalization.lean:595, 147）= **標準の環局所化**。
- ゆえに `q3Ring = ℤ₃[1/3]` は**実 ℤ₃ の 3 冪局所化＝本物の ℚ₃**。RingLocalization の実例代入で
  あり機構再証明はしていない（正しい流儀）。**コードベース初の p 進体オブジェクトは本物**。
- **∃ 形体性 q3f_has_inverses は本物**: 非零 witness `¬z3vGe a (k+1)` 付き分子 mk(a,3ⁿ) の
  逆元を `z3v_extract`（a=3^v·u 分解）＋明示逆元 `zpUnitInv`（choice-free 関数・zpUnitInv_mul で
  逆元証明済み）で **明示構成**。∃ の witness は Classical でなく具体式。[propext,Quot.sound]。
- `q3f_uniformizer`: 3 は v=1 の厳密付値かつ ℤ₃ の単数でない（本物・9∤3 を quot_exact で）。
- `q3f_ring_of_val`: v≥0 の元は分母 3⁰ で表せる＝O=ℤ₃（zpDivP 反復で分子から 3^n を剥がす・本物）。

## 2. complete_note「K_v 皆無」の discharge は本物か — YES（ただし体でなく体オブジェクト）

前回 0.5 の唯一の欠落名指し「実 p 進局所体 K_v も皆無」は、**ℚ₃=ℤ₃[1/3] という実体が
存在しなかった**ことを指す。今回それが本物に建った（§1）。よって discharge は本物。
ただし後述の通り **ℚ₃ は IUTField（total inv 持つ体）ではなく、∃ 形逆元を持つ CRing 体
オブジェクト**である。「K_v 皆無」は解消したが「K_v 完成」ではない（0.65 の理由）。

## 3. 付値環・剰余体が本物か — YES

- `z3v_extract`（x=3^v·u 分解）は **本物・choice-free**: 実 Hensel 帰納 `zpValDecompose`
  （ZpDomain.lean:224・decidable なレベル1ゼロ判定 zmodIsZero で分岐する構造帰納・zpDivP 再帰）
  を消費。witness は再帰構成で choice なし。
- `z3vMaximal`（極大イデアル 3ℤ₃・局所環性）は **本物**: `resFieldMaximal`（proper +
  witness 形極大性 maximal_witness: x∉m→∃r s, s∈m ∧ r·x+s=1）の実インスタンス。3ℤ₃={v≥1}
  を primeSpecIdeal に代入し、極大性 witness は r=zpUnitInv（明示逆元）・s=0 で即納。
  **体でない環における resFieldMaximal 機構への初の非自明実例**（従来は体の零イデアルのみ）。
- `z3v_res_iso`（剰余体≅𝔽₃）は **本物**: z3vResToF3 と z3vF3ToRes の双方向 RingHom を
  z3v_f3ToRes_resToF3 / z3v_resToF3_f3ToRes（左右逆）で恒等証明。genuine な環同型。
- `f3Field`（有限 IUTField）は **本物**: 台=zmodRing 3、total inv=恒等。mul_inv_cancel は
  x≠0⟹3∤a を Quot.ind で開き a%3∈{1,2} の 2 枝で (a−1)(a+1)=a²−1 の一方が 3 の倍数から証明
  （f3_diff_sq は Int core の分配律のみ）。inv=id は p=3 特有（(ℤ/3)^×={±1} 位数2で x²=1）で
  **判定不要に total inv が書ける正当なケース**（§3.1 の Markov 障害には抵触しない有限分岐）。
  [propext,Quot.sound]。コードベース初の有限 IUTField として正しい。

## 4. 完備性・付値接続が本物か — YES（modulus 形＝正直な限定）

- `z3cLim` は modulus 付き Cauchy 列 (x,M) の極限をレベルごと閉じた式 (x(M' n)).val n で構成
  （整合性は成分計算のみ）。`z3c_converges`（レベルごと収束）・`z3c_lim_unique`（分離性）・
  `z3c_int_dense`（ℤ 稠密）すべて本物・choice-free。∃ の収束仮定は Prop 消費（obtain）のみで
  極限構成に choice を持ち込まない。**∃形 Cauchy でなく modulus 入力形＝正直な限定**（∀n∃N からの
  modulus 抽出は可算選択を要するため後続と honest 明記・消していない）。
- `z3c_val_compat`（実 pvq 付値＝ℤ₃ 内付値）は **本物の境界接着**: 非零整数 a に対し実 ℚ 側の
  本物 3 進付値 pvqNatVal 3 |a| = ℤ₃ 内 z3vExact(toZp a)。prime_pow_extract で a=3^k·m'（3∤m'）に
  開き pvqNatVal_spec で左辺=k、右辺は Int↔Nat 整除の橋渡しで k での整除・k+1 での非整除を証明。
  **付値機構（本物 pvq）と完備化体（実 ℤ₃）の境界を実接着**。[propext,Quot.sound]。

## 5. 過大主張の検出（core 判定）— 過大主張なし・honest 限定は全て健在

- **total inv を密かに主張していないか（choice 違反の有無）— していない（確認済み）**:
  Q3LocalField/Q3UnitsGroup に `q3Ring` への IUTField/Field インスタンスは**皆無**
  （grep で IUTField 言及は header の「total inv は主張しない」note のみ・`inv :=` の total 体定義なし）。
  ℚ₃ は ∃ 形逆元（q3f_has_inverses）のみ。**total inv を付けていない＝choice 違反なし**。#print
  axioms でも q3Ring 推移閉包に Classical.choice 無し。
- ヘッダ記載の honest 限定を grep で裏取り、すべて健在・消去弱化なし:
  total inv 不可（§3.1・∃ 形が忠実版・Markov 却下）／IUTField としての ℚ₃ は非主張／p=3 固定／
  ℚ↪ℚ₃（A2c-3）未接続／∃形 Cauchy 完備性・位相・G_{ℚ₃} 範囲外。q3u は既存 surrogate
  （QpUnits/prodGrp）を消さず昇格の形。
- **付値は関数でなく関係**（z3vGe/z3vExact・q3fValRel）＝逆極限モデル固有の忠実版。過大でない。

## 6. なぜ 0.65 か（0.7 を超えない・0.6/0.62 まで下げない理由）

設計 A2-detail の 0.65 は A2a（ℤ₃ DVR package + 𝔽₃）+ A2b（modulus 完備性 + val_compat）+
A2c（ℚ₃ 体オブジェクト + ∃ 形体性 + uniformizer + O=ℤ₃ + ℚ₃^×）**全部が本物・choice-free に
landing した場合の上限**。自走検証の結果、**全ピースが設計どおり landing し、いずれも
[propext,Quot.sound]・total inv 非主張・honest 限定健在**であることを確認した。

- **0.7 を超えない理由（0.65 上限を画定する 3 つの本物ギャップ）**: (i) ℚ₃ は total inv を持つ
  IUTField ではなく ∃ 形逆元の CRing 体オブジェクト（ℚ_p は構成的に離散体でない恒久障害）、
  (ii) ℚ↪ℚ₃ の体埋め込み（A2c-3）が未接続で「K の完備化」の K との体レベル接続は
  z3c_val_compat の整数付値一致どまり、(iii) ℚ₃ の位相・G_{ℚ₃}・分岐（IUT が実際に要する局所体の
  Galois 側）が皆無。これら 3 つは設計が 0.65 の cap 理由として名指したものと一致し、実在を確認。
- **0.6/0.62 まで下げない理由**: 上記 3 ギャップは 0.65 の cap にすでに織り込まれた限定であり、
  同じ理由で再度減点するのは二重計上。前回 0.5「K_v 皆無」から、実 ℚ₃ 体オブジェクト＋完備性定理＋
  剰余体 𝔽₃ 同型＋ℚ₃^× 埋め込みの **4 つの独立な本物構成**が landing した質的前進は、
  「0.5 の忠実な部分ケースを質的に超える」（_status_scale の中間値条件）を明確に満たす。
  0.6 は完備性・体オブジェクト・剰余体・単数群が全部本物に入った事実を過小評価する。
- 兄弟校正との整合: A1=0.85（総 inv + 一般構成器 + 基底）・A3=0.75（逆極限 profinite + レベル同型）
  に対し、A2=0.65（体オブジェクト + ∃ 形 + 完備性・total inv/位相/Galois 未）は序列として妥当。

## 7. 柱A% の算定（丸め境界の確定）

Σ(w·s) 分母=100（柱A weight 総和）。現状（A2=0.5）: Σ=44.7 → 45。
A2=0.65: Σ=44.7 − 8·0.5 + 8·0.65 = 44.7 + 1.2 = **45.9 → round=46**（安定・45.5 の不安定境界を回避）。
（参考: A2=0.6 なら 45.5＝丸め不安定境界、A2=0.62 なら 45.66→46。0.65 は 45.9 で安全圏。）
**柱A% 45 → 46（+1）**。compute_complete_pct.py で確認。

## 8. 反映（監査確定分のみ・IUT/*.lean は不変更）

- target_ledger.json: A2 status 0.5 → **0.65**、`_current_numerator` に本監査トレイル追記。
- graph-meta.json: pillars.A.complete_pct 45 → **46**、complete_note の「実p進局所体K_vも皆無」を
  「実 ℚ₃=ℤ₃[1/3] 体オブジェクト＋完備性＋剰余体𝔽₃＋ℚ₃^× を実構成（total inv/位相/G_{ℚ₃}/
  ℚ↪ℚ₃ は未・∃形体性）」へ更新、_last_round 更新。
- tools/compute_complete_pct.py で柱A=46 を確認、tools/gen_graph.py で graph.json 再生成。
- dashboard.md 二軸表を同期。

## 残る限定（正直申告・次の 0.7 への道）

total inv（構成的に不可・恒久 honest）／ℚ↪ℚ₃ 体埋め込み（A2c-3）／∃形 Cauchy・位相的完備性／
ℚ₃ の位相・G_{ℚ₃}・分岐理論（B1 射程）／p=3・基礎体 ℚ 固定。0.7 以上は ℚ↪ℚ₃ ＋（位相 or
M311F 機構との比較定理）を要する。
