#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gen_graph.py — IUT-Lean 依存グラフのデータ生成（stdlib のみ）

iut-lean-verification/ の Lean ソースを解析し、インタラクティブ
グラフ（index.html / Cytoscape）が読み込む graph.json を生成する。

抽出するもの:
  - ノード集合: IUT.lean の `import IUT.X` 並び（= 全モジュールの正準集合）
  - 依存エッジ: 各 IUT/X.lean 冒頭の `import IUT.Y`（依存 Y → 被依存 X の有向辺）
  - マイルストーン id・タイトル: ヘッダコメント（行頭の `IUT/X.lean — Mxx（…）`）
  - choice-free フラグ: 「選択公理不使用」/「choice なし」の有無
  - 正直申告フラグ: 「正直」/「未形式化」/「対象外」の有無
  - 文献トークン: [EtTh] / [FrdI] 等の引用
  - 宣言数 decl_count: theorem/lemma/def/structure/instance/abbrev の本数（ノード重み）
  - 柱（pillar）: 下記 PILLAR マップ（構造的・正準）

per-theorem の build.sh ロスター（1022 件）はドット名前空間でファイルに
紐付かないため、ノード単位の属性化は行わず、総数のみ headline 統計に使う。

実行: iut-lean-verification/ で `python3 tools/gen_graph.py`
出力: iut-lean-verification/graph.json
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent          # iut-lean-verification/
IUT_DIR = ROOT / "IUT"
GH_BASE = ("https://github.com/bottlenome/onepagers/blob/main/"
           "iut-lean-verification/IUT/")

# --- 柱（pillar）正準マップ: module -> code ---------------------------------
# core=論争骨格 / A=基本群・Galois圏(基盤) / B=局所類体論 / C=Lubin–Tate・形式群・Frobenioid
# D=定理3.11 / E=幾何層(theta/volume)
PILLAR = {
    # core（論争骨格・メタ）
    "Arithmetic": "core", "Skeleton": "core", "ScholzeStix": "core",
    "Mochizuki": "core", "Boolean": "core", "Verdict": "core",
    "HodgeTheater": "core", "LogThetaLattice": "core", "AbcConsequences": "core",
    # 柱A（基盤: 基本群・Galois圏・SGA1）
    "Anabelian": "A", "FundamentalGroup": "A", "Reconstruction": "A",
    "EtaleTheta": "A", "Profinite": "A", "GaloisCategory": "A", "Topology": "A",
    "SGA1": "A", "Finiteness": "A", "Compactness": "A", "CategoryTheory": "A",
    "GaloisAxioms": "A", "AbstractGalois": "A", "SGA1Completion": "A",
    "SGA1Object": "A", "ProObject": "A", "LimitCompact": "A", "SumDecomposition": "A",
    "FlUnits": "A",
    "FlStar": "A",
    "FlStarCount": "A",
    # 柱B（局所類体論・Eisenstein）
    "LocalCFT": "B", "NormCorrespondence": "B", "PrincipalUnits": "B",
    "PrincipalUnitGroup": "B", "UnitFiltration": "B", "Fermat": "B",
    "Teichmuller": "B", "RootsOfUnity": "B", "UnitDecomposition": "B",
    "ZpUnits": "B", "FullReciprocity": "B", "ZpDomain": "B", "TorsionTrivial": "B",
    "EisensteinRing": "B", "EisensteinTorsion": "B", "EisensteinConjugates": "B",
    "RamifiedEntrance": "B", "EisensteinGalois": "B", "RecRamified": "B",
    "EisensteinTower": "B", "EisensteinUpper": "B", "EisDomain": "B",
    "EisDomain2": "B", "EisEndoRigidity": "B", "FactorTheorem": "B",
    "LambdaClassify": "B", "RecGluing": "B", "FormalGroupEndRing": "B",
    "MuUnits": "B",
    "ZmodOrder": "B", "NatPrimeParts": "B", "PrimitiveRoot": "B",
    "CyclicUnits": "B",
    "LambdaModule": "B",
    "LambdaSemilinear": "B",
    "RamifiedReciprocity": "B", "PadicSeries": "B", "EisTowerRings": "B", "PadicSeries2": "B",
    "ResidueTower": "B", "ZpUnitDecomp": "B", "TowerTorsion": "B", "TorsionResidue": "B",
    "PadicGeometric": "B",
    # 柱C（Lubin–Tate・形式群・Frobenioid）
    "Ring": "C", "PowerSeries": "C", "Composition": "C", "LubinTateUnique": "C",
    "LubinTateZp": "C", "PadicDivision": "C", "Binomial2": "C", "Freshman": "C",
    "PSFunctor": "C", "FrobeniusCharP": "C", "LTErrorDivisible": "C",
    "LubinTateExists": "C", "Frobenioid": "C", "FrobenioidCat": "C",
    "FrobenioidModel": "C", "PolyIsomorphism": "C", "SplitFrobenioid": "C",
    "FiberedFrobenioid": "C", "SplitFibered": "C", "RamifiedBase": "C",
    "RamifiedSplit": "C", "PowerSeries2": "C", "FormalGroupSub": "C",
    "FormalGroupEq": "C", "FormalGroupMap": "C", "FrobeniusGen": "C",
    "Frobenius2": "C", "FormalGroupErr": "C", "FormalGroupCongr": "C",
    "FormalGroupDecomp": "C", "FormalGroupDiag": "C", "FormalGroupExists": "C",
    "FormalGroupUnique": "C", "FormalGroupComm": "C", "PowerSeries3": "C",
    "FormalGroup3Congr": "C", "FormalGroup3Decomp": "C", "FormalGroup3Unique": "C",
    "FormalGroupAssocDef": "C", "FormalGroupChain": "C", "FormalGroupFam": "C",
    "FormalGroupMult": "C", "FormalGroupComp1": "C", "FormalGroupComp2": "C",
    "FormalGroupBridge": "C", "FormalGroupMult3": "C", "FormalGroupLift": "C",
    "FormalGroupComp3": "C", "FormalGroupAssoc": "C", "FormalGroupEval": "C",
    "FormalGroupEvalMult": "C", "FormalGroupEvalComp": "C", "LTIterate": "C",
    "FormalGroupInverse": "C", "FormalGroupOModule": "C", "FormalGroupInvLeft": "C",
    "FormalGroupEnd": "C", "FormalGroupPoints": "C", "PointValues": "C",
    "FormalGroupPointsMul": "C", "FormalGroupPointsComp": "C", "FormalGroupPoints2": "C",
    "TorsionPoints": "C", "FormalGroupPointsLaw": "C", "FormalGroupPoints3": "C",
    "FormalGroupPointsMul2": "C", "FormalGroupPointsMul3": "C",
    "FormalGroupPointsAssoc": "C", "DecompositionInertia": "C", "Realification": "C",
    "ArchimedeanPlace": "C", "Rationals": "C", "RegularReal": "C",
    # 柱D（定理3.11）
    "Multiradial": "D", "Diophantine": "D", "Premises311": "D", "VolumeModel": "D",
    # 柱E（幾何層: theta/volume）
    "Evaluation": "E", "LaurentCoeff": "E", "LaurentRing": "E", "LaurentMonomial": "E",
    "ThetaSeries": "E", "ThetaFunctional": "E", "ThetaReflection": "E",
    "ThetaGauss": "E", "TateQuotient": "E", "MonoThetaWitness": "E",
    "ThetaGroupMod": "E", "GaussianVolume": "E", "ThetaPM": "E",
}

# マイルストーン id を持たない初期ファイルのフォールバック
FALLBACK = {
    "Arithmetic": ("M0", "算術の骨格（高さ・ABC・Szpiro の枠組み）"),
    "Skeleton": ("M0", "系3.12 論争の形式骨格"),
    "ScholzeStix": ("S1", "Scholze–Stix の読み（RC 同一視）"),
    "Mochizuki": ("R1", "望月の読み（同一視拒否）"),
    "Boolean": ("M0", "命題論理の土台"),
    "Verdict": ("M6", "二分法の最終判定（verdict）"),
}

REF_TOKENS = ["[EtTh]", "[FrdI]", "[FrdII]", "[AbsTopIII]",
              "[IUTchI]", "[IUTchII]", "[IUTchIII]", "[IUTchIV]",
              "[SemiAnbd]", "[GenEll]"]

DECL_RE = re.compile(r"^(?:theorem|lemma|def|structure|instance|abbrev)\s")
IMPORT_RE = re.compile(r"^import\s+IUT\.(\S+)\s*$")
MS_EMDASH = re.compile(r"[—–-]\s*(M\d+\w*)")          # IUT/X.lean — M100（…
MS_COLON = re.compile(r"^\s*#*\s*(M\d+\w*)\s*[:：]\s*(.*)$")  # M70c: … / # M111: …
TITLE_PAREN = re.compile(r"(M\d+\w*)[（(]([^）)]+)")   # Mxx（タイトル…）


def read_modules():
    mods = []
    for line in (ROOT / "IUT.lean").read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(line.strip())
        if m:
            mods.append(m.group(1))
    return mods


def header_block(text):
    start = text.find("/-")
    end = text.find("-/", start + 2)
    return text[start:end] if start != -1 and end != -1 else text[:1500]


def parse_module(name):
    path = IUT_DIR / f"{name}.lean"
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    # edges (import region = before first decl/namespace)
    deps = []
    for line in lines:
        m = IMPORT_RE.match(line.strip())
        if m:
            deps.append(m.group(1))
    header = header_block(text)
    # milestone id
    ms = None
    colon_title = None
    m = MS_EMDASH.search(header[:400])
    if m:
        ms = m.group(1)
    else:
        for ln in header.splitlines()[:6]:
            m2 = MS_COLON.match(ln.strip())
            if m2:
                ms = m2.group(1)
                colon_title = m2.group(2).strip()
                break
    # title
    title = None
    mt = TITLE_PAREN.search(header[:400])
    if mt and (ms is None or mt.group(1) == ms):
        title = mt.group(2).strip().rstrip("：:、 ")
    if title is None and colon_title:
        title = colon_title.split("—")[0].strip().rstrip("：:、 ")
    if title is None and ms:
        # 「… — Mxx: タイトル — …」形式（emdash 見出し + コロン）
        mc = re.search(re.escape(ms) + r"\s*[:：]\s*([^\n]+)", header[:400])
        if mc:
            title = mc.group(1).split("—")[0].strip().rstrip("：:、 ")
    if title is not None:
        title = re.sub(r"\s+", " ", title)
    if (ms is None or title is None) and name in FALLBACK:
        fms, ftitle = FALLBACK[name]
        ms = ms or fms
        title = title or ftitle
    if title is None:
        title = name
    # flags
    choice_free = ("選択公理不使用" in text) or ("choice なし" in text)
    honest = any(k in header for k in ("正直", "未形式化", "対象外"))
    refs = [t for t in REF_TOKENS if t in text]
    decl_count = sum(1 for ln in lines if DECL_RE.match(ln))
    return {
        "id": name,
        "label": name,
        "milestone": ms,
        "title": title,
        "pillar": PILLAR.get(name, "unassigned"),
        "decl_count": decl_count,
        "choice_free": choice_free,
        "has_honest_scope": honest,
        "refs": refs,
        "github_url": GH_BASE + name + ".lean",
    }, deps


def main():
    mods = read_modules()
    modset = set(mods)
    nodes, edges = [], []
    for name in mods:
        node, deps = parse_module(name)
        nodes.append(node)
        for d in deps:
            if d in modset:
                edges.append({"source": d, "target": name})
    edges.sort(key=lambda e: (e["source"], e["target"]))
    # build.sh の検証済み定理総数（headline 統計のみ）
    bs = (ROOT / "build.sh").read_text(encoding="utf-8")
    verified_total = sum(1 for ln in bs.splitlines()
                         if ln.strip().startswith("#print axioms IUT."))
    out = {
        "generated_from": "IUT.lean + IUT/*.lean + build.sh",
        "module_count": len(nodes),
        "verified_theorem_total": verified_total,
        "choice_free_count": sum(1 for n in nodes if n["choice_free"]),
        "nodes": nodes,
        "edges": edges,
    }
    (ROOT / "graph.json").write_text(
        json.dumps(out, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    # 簡易サマリ
    from collections import Counter
    pc = Counter(n["pillar"] for n in nodes)
    print(f"modules={len(nodes)} edges={len(edges)} "
          f"verified_theorems={verified_total} "
          f"choice_free={out['choice_free_count']}")
    print("pillars=" + " ".join(f"{k}:{v}" for k, v in sorted(pc.items())))
    miss = [n["id"] for n in nodes if n["pillar"] == "unassigned"]
    if miss:
        print("UNASSIGNED:", miss)


if __name__ == "__main__":
    main()
