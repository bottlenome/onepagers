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
    "ResidueTower": "B", "ZpUnitDecomp": "B", "TowerNonzero": "B", "EisFaithful": "B", "TowerTorsion": "B", "TorsionResidue": "B",
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
    "ArchimedeanPlace": "C", "Rationals": "C", "RegularReal": "C", "RatFloor": "C", "RealMul": "C", "RealOrder": "C", "RealAbs": "C", "RealComplete": "C", "RealPosMul": "C", "RealLe": "C", "LogVolBridge": "C",
    # 柱D（定理3.11）
    "Multiradial": "D", "Diophantine": "D", "Premises311": "D", "VolumeModel": "D",
    # 柱E（幾何層: theta/volume）
    "Evaluation": "E", "LaurentCoeff": "E", "LaurentRing": "E", "LaurentMonomial": "E",
    "ThetaSeries": "E", "ThetaFunctional": "E", "ThetaReflection": "E",
    "ThetaGauss": "E", "TateQuotient": "E", "MonoThetaWitness": "E",
    "ThetaGroupMod": "E", "GaussianVolume": "E", "ThetaPM": "E", "MuLSubgroup": "E", "CyclotomicSync": "E", "ThetaCenterMod": "E", "VolumeReal": "E", "GaussianDivisor": "E", "Premises311Real": "D", "WeightedGauss": "E", "RealOrderComplete": "C", "FuneqLift": "E", "ScalarDistrib": "C", "RealVolumeTheory": "D", "RealMaxLaws": "C", "GaussPilotRep": "D", "IntRealBridge": "C", "TriSquare": "E", "LambdaPropagation": "B", "RegularPowers": "B", "PolyWeierstrass": "B", "GaloisClosureModel": "A", "GSetQuotient": "A", "RealInv": "C", "LambdaValuation": "B", "PolyDivision": "B", "ApartInv": "C", "RealRingLaws": "C", "CosetGalois": "A", "TowerSeparation": "B", "RealFieldCapstone": "C", "FactorialTower": "A", "GaussPilotWeighted": "D", "RealObstruction": "D", "LambdaValuationMul": "B", "RealDivision": "C", "GeomSeries": "C", "LambdaIdeal": "B", "RealGeom": "C", "RealPow": "C", "RealPowMul": "C", "RealGeomRec": "C", "RealAbsPow": "C", "GeomSeriesRec": "C", "RealGeomCongr": "C", "LambdaGeom": "B", "RealAbsLe": "C", "RealAbsTriangle": "C", "RealGeomAbs": "C", "LambdaInvApprox": "B", "RealGeomInv": "C", "GeometricSeriesProgram": "C", "GeomDecayNat": "C", "RealMulOrder": "C", "RealGeomDecay": "C", "GeomConverge": "C", "GeomLimit": "C", "GeomConvergeSC": "C", "GaloisClosureLift": "A", "EisSeparation": "B", "AbstractEssSurj": "A", "MuLIdentification": "E", "GeomRlimComplete": "C", "AbstractEssSurjSum": "A", "ThetaHeisenbergLift": "E", "TateCoverGroup": "A", "AbstractGaloisDomination": "A", "ThetaFuneqBridge": "E", "MuP1Cyclic": "B", "LambdaTowerGen": "B", "EssSurjCapstone": "A", "TateCoverCat": "A", "MonoThetaEnv": "D", "ConvergenceCapstone": "C", "TateCoverGalois": "A", "RecRamifiedSurj": "B", "ThetaOperatorHom": "E", "LogShell": "D", "TateFiberFunctor": "A", "Indeterminacies": "D", "LambdaTowerTrans": "B", "ThetaChainCapstone": "E", "TateSurrogateCapstone": "A", "RecUnramified": "B", "ThetaValueEval": "E", "LogKummer": "D", "FormalEndRing": "B", "Multiradial311": "D", "PillarDFoundation": "D", "ThetaLabelInjective": "E", "LambdaTowerExactVal": "B", "ProRepresentable": "A", "MultiradialInput": "D", "GaussPilot311": "D", "RecSurjective": "B", "ThetaEvalCapstone": "E", "GaloisEquivalence": "A", "PillarDInterface": "D", "FormalGroupCapstone": "C", "ThetaValueConstruct": "E", "LambdaTowerRamif": "B", "GaloisFullness": "A", "LambdaTowerExactRamif": "B", "InputConverse": "D", "RealMultiradialInput": "D", "GaloisEquivalenceBundle": "A", "PillarDBetaLocalization": "D", "FormalGroupPointLaws": "C", "ThetaRingObject": "E", "FrobenioidVolume": "D", "GaloisEquivalenceUncond": "A", "ThetaValueSubgroup": "E", "NNQtoQHom": "C", "NNQMulHom": "C", "NNQSemiring": "C", "LambdaTowerPiValBound": "B", "GaloisFullnessConnected": "A", "ArithPilot": "D", "LambdaTowerRamifCapstone": "B", "LambdaTowerPiValGeom": "B", "LogVolEffMono": "C", "ThetaValueProdLaws": "E", "IndAction": "D", "ThetaValueAlgebra": "E", "ThetaLinkTransport": "D", "FormalGroupPointOAction": "C", "LambdaTowerResidueSurj": "B", "GSetCoequalizer": "A", "ThetaValueProdSwapAt": "E", "ThetaValueProdPerm": "E", "IntermediateNormalCover": "A", "FormalGroupPointODerived": "C", "LambdaTowerResidueKernel": "B", "TransportMirror": "D", "ThetaValueProdBlockSwap": "E", "FormalGroupOModulePoint": "C", "LambdaTowerResidueKernelConverse": "B", "NormalPairBoundary": "A", "IndActionLabel": "D", "PillarAFullnessProgram": "A", "ThetaValueProdRangeSplit": "E", "IndActionFull": "D", "NNQOrder": "C", "LambdaTowerResidueKernelTower": "B", "Field": "A", "QuotientGroup": "A", "ProfiniteTopology": "A", "PolyFieldDivision": "A", "FractionField": "A", "FieldAutGroup": "A", "SeparablePoly": "A", "FiniteEtaleAlgebra": "A", "MinimalPolynomial": "A", "SimpleExtension": "A", "FiberFunctor": "A", "EvaluationHom": "A", "RootAdjunction": "A", "GrothendieckGalois": "A", "AlgebraTensor": "A", "IdempotentSpectrum": "A", "GaloisCorrespondence": "A", "SeparableEmbeddings": "A", "TowerLaw": "A", "ConnectedEtale": "A", "ProfinitePi1": "A", "NormalSplitting": "A", "GaloisPi1Iso": "A", "GaloisFundamental": "A", "PrimitiveElement": "A", "SpecFunctorial": "A", "ZariskiConnected": "A", "PrimeSpectrum": "A", "RingLocalization": "A", "StructureSheafBasic": "A", "FunctorOfPoints": "A", "GlobalSectionsRecover": "A", "LocalRingStalk": "A", "ResidueField": "A", "NilradicalReduced": "A", "AffineEquivFull": "A", "IntegralExtension": "A", "FractionalIdeal": "A", "RingOfIntegers": "A", "ValuationRing": "A", "DedekindDomain": "A", "LocalFieldCompletion": "B", "EllipticCurve": "A", "EtaleThetaReal": "E", "PicardDivisor": "C", "EllipticJInvariant": "A", "ThetaJacobi": "E", "LogVolume": "C", "TateCurve": "A", "LocalFieldRing": "B", "LogVolumeArch": "C", "TateTorsion": "A", "AlgClosureColimit": "A", "FieldCompletion": "B", "ThetaValueLtor": "E", "ThetaPilotRealVolume": "D", "KummerTheory": "B", "MonoThetaRigidity": "E", "LogShellReal": "C", "CyclotomicRigidity": "A", "AbsTopMultAdd": "A", "GaussPilotRealVolume": "D", "LogKummerReal": "C", "ThetaLinkReal": "E", "GaloisCohomologyH1": "B", "AbsTopFieldRecover": "A", "LocalReciprocity": "B", "FrobenioidCategory": "C", "IndeterminacyRealAction": "D", "DiscreteRigidity": "E", "LogLinkReal": "D", "CyclotomeRecovery": "A", "NormGroup": "B", "ThetaCyclotomicRigidity": "E", "HaarMeasureZp": "C", "MeasureLogVolume": "C", "Hilbert90": "B", "IndeterminacyFull": "D", "WeilPairing": "A", "GaloisTheta": "E", "CruxInequalityReal": "D", "ThetaMuTorsor": "E", "WeilGaloisEquiv": "A", "KummerExact": "B", "ArchHaarVolume": "C", "SzpiroReduction": "D", "ProductFormula": "C", "KummerCharReal": "A", "ThetaKummerClass": "E", "CupProduct": "B", "ThetaKummerRigidity": "E", "WeilKummerDuality": "A", "ArakelovDivisor": "C", "ABCConsequence": "D", "CupGradedComm": "B", "FrobArakelovBridge": "C", "LocalBrauer": "B", "MultiradialCompare": "D", "MonoThetaEnvironment": "E", "AbsTopMultMonoid": "A", "QuadraticProductFormula": "C", "LogLinkIndeterminacy": "D", "ThetaGaloisOrbit": "E", "BrauerInvariant": "B", "TemperedPi1": "A", "MultiradialRep": "D", "ThetaCovering": "A", "HilbertSymbol": "B", "DifferentDiscriminant": "C", "ThetaOrbitProduct": "E", "ThetaPilotOrbitBridge": "E", "CyclotomicDiscriminant": "C", "LogKummerMonoTheta": "D", "TameSymbol": "B", "TemperedTower": "A", "CyclotomicDifferent": "C", "TemperedCommutator": "A", "ThetaRigidityBridge": "E", "MultiradialIndet": "D", "LubinTate": "B", "CyclotomicPrimePower": "C", "TemperedThetaCommutator": "A", "LubinTateReciprocity": "B", "LogShellContainment": "D", "MonoThetaTripleBridge": "E", "LogLinkShellCompat": "D", "ThetaKummerTripleBridge": "E", "LubinTateNormGroup": "B", "ConductorDiscriminantAbelian": "C", "TemperedThetaOuterAction": "A", "ThetaValueTripleBridge": "E", "ThetaGroupReconstruction": "A", "RingOfIntegersDiscriminant": "C", "LogThetaLatticeShell": "D", "BrauerInvariantFull": "B", "ThetaValueOrbitBridge": "E", "ReciprocityBrauerCompat": "B", "MultiradialLatticeCompare": "D", "DiscriminantLowerBound": "C", "ThetaGroupRigidity": "A", "ThetaOrbitProductBridge": "E", "ThetaLinkMultiradial": "D", "CyclotomeGaloisModule": "A", "ReciprocityNondegenerate": "B", "IdealClassGroup": "C", "ThetaOrbitVolumeBridge": "E", "AbsTopFieldFromCyclotome": "A", "PilotComparisonMultiradial": "D", "FrobenioidRealification": "C", "HilbertSymbolReciprocity": "B", "ThetaPilotGaussBridge": "E", "AbsTopFullRecovery": "A", "FrobenioidLinkDegree": "C", "LogVolumePilotBound": "D", "HigherUnitFiltration": "B", "MonoThetaKummerBridge": "E", "RamifiedNormFiltration": "B", "ClassNumberFiniteness": "C", "KummerReconstructedField": "A", "PilotVolumeUpperContainment": "D", "ThetaCommutatorValueBridge": "E", "DifferentFromFiltration": "B", "PilotBoundMultiradialFull": "D", "ArakelovClassDegree": "C", "TemperedPi1Etale": "A", "ArtinConductor": "B", "ThetaClassCommutatorBridge": "E", "LogVolMultiradialTransport": "D", "ArakelovPicExact": "C", "ArithTemperedPi1": "A", "ConductorDiscriminant": "B", "ArakelovArithDegree": "C", "ThetaCommTemperedBridge": "E", "MultiradialLogLinkTransport": "D", "ThetaLinkTemperedPi1": "A", "LogLinkIndetNonzero": "D", "ThetaLinkTwoTheater": "A", "ArakelovIntersectionPairing": "C", "WildConductorDiscriminant": "B", "CyclotomeIdentification": "E", "ArakelovGreenArch": "C", "LogLinkFullIndetGroup": "D", "MultiJumpWildDiscriminant": "B", "KummerCharWiring": "E", "ThetaLinkPolyIso": "A", "LogLinkContinuousIndet": "D", "GreenCurvature": "C", "ArbitraryJumpWild": "B", "FrobenioidThetaLink": "A", "KummerNontrivialChar": "E", "HasseArfUnconditional": "B", "GreenCurvature2D": "C", "LogLinkFullContinuous": "D", "FrobenioidLogThetaLattice": "A", "KummerGeneralChar": "E", "HasseArfAbelian": "B", "GreenAnisotropic": "C", "IndetHaarIntegral": "D", "ZmodInverseBezout": "E", "InfiniteLogThetaLattice": "A", "CoprimalityDecision": "E", "HasseArfFiniteAbelian": "B", "LatticeCoherenceIndet": "A", "GreenVariableCoeff": "C", "IndetHaarLimit": "D", "ArtinConductorHigherDim": "B", "GreenVariableSolve": "C", "LatticeCoherenceContinuous": "A", "NonUnitConstructive": "E", "HaarNonconstantConverge": "D", "GaussianRationalField": "A", "QuadraticField": "A", "QuadraticNorm": "B", "ArchAbsValueQ": "C", "PadicValuationQ": "D", "CyclotomicFieldQ3": "E", "PrimeFactorization": "B", "PadicAbsValueQ": "B", "FiniteSupportPrimeProduct": "B", "ArchValueInteger": "B", "B5ProductFormulaQ": "B", "CubeRootTwoIrrational": "A", "CubicPolyQ": "A", "PolyBezoutQ": "A", "RatZeroDecide": "A", "PolyPSUtil": "A", "CbrtTwoBase": "A", "CbrtLinearFactor": "A", "CbrtBezB": "A", "CbrtCofactor": "A", "CbrtBezoutChain": "A", "CbrtTwoField": "A", "CbrtTwoAlpha": "A", "PolyDivisibility": "A", "PolyIrreducible": "A", "PolyLeadOracleQ": "A", "Cq3Base": "A", "Cq3BezoutChain": "A", "Cq3Field": "A", "Cq3Alpha": "A", "PolyDvdBounded": "A", "PolyBezoutBounded": "A", "PolyIrreducibleBounded": "A", "GenExtField": "A", "CbrtTwoIrreducible": "A", "Cq3Irreducible": "A", "GenFieldInstances": "A", "PolyLeadFindQ": "A", "PolyDivModFn": "A", "PolyMonomialBasis": "A", "PolyEuclidFn": "A", "GenExtFieldNF": "A", "GenExtFieldInv": "A", "GenExtBasisAlpha": "A", "GenExtTower": "A", "CyclotomicPolyData": "A", "PolyRootCount": "A", "PadicUltrametricQ": "A", "Phi9Shift": "A", "CyclotomicField3": "A", "CyclotomicGal3": "A", "GaussValuationQ": "A", "EisensteinCriterionQ": "A", "Phi9Irreducible": "A", "CyclotomicMu9": "A", "CyclotomicEmbed39": "A", "CyclotomicMu9Roots": "A", "CyclotomicRes39": "A", "CyclotomicStretch": "A", "CyclotomicGal9": "A", "EisensteinShiftTransport": "A", "CyclotomicSurj39": "A", "EisensteinTowerInput": "A", "CyclotomicEmbedTower": "A", "CyclotomicMuTower": "A", "CyclotomicAutExt": "A", "CyclotomicSubAut": "A", "CyclotomicResTower": "A", "CyclotomicTowerLimit": "A", "Zmod3PowUnits": "A", "Zmod3PowUnitsSystem": "A", "CyclotomicCharIso": "A", "CyclotomicLimitIso": "A", "CyclotomicProjSurj": "A", "CyclotomicMuGroupReal": "A", "CyclotomicGKActionReal": "A", "CyclotomicRigidityAut": "A", "TateModuleZ3": "A", "CyclotomeRecoveryReal": "A", "F3Field": "A", "Zp3ValuationRing": "A", "Zp3Complete": "A", "Q3LocalField": "A", "Q3UnitsGroup": "A", "Q3TateCurve": "A", "Q3TateTorsion": "A", "Q3TateDeck": "A", "Q3TemperedPi1": "A", "TateModuleEndo": "A", "TateModuleIndeterminacy": "A", "Q3TateCoverTower": "A", "Q3TatePi1Etale": "A", "Q3TatePi1Comparison": "A", "Q3TemperedPi1Deepen": "A", "Q3RatFieldEmbed": "A", "Q3TateCubeIsogeny": "A", "BelyiCubicRamification": "A", "TateModuleEndoRing": "A", "CyclotomeRecoveryThetaKill": "A", "BelyiCubicReal": "A", "CyclotomeRecoveryLimit": "A", "CyclotomeRecoveryCanonicity": "A", "CyclotomeRecoveryTorsor": "A", "Q3TateCuspidalization": "A", "Q3ThetaGroup": "A", "Q3TemperedThetaClass": "A", "Q3MonoThetaRigidity": "A", "Q3RamifiedQuadratic": "A", "Q3Mu3Completeness": "A", "Q3TateCurveL2": "A", "Q3Mu3ThetaGroup": "A", "Q3Mu3Rigidity": "A", "Q3Mu3TmzBridge": "A", "Q3KummerCubic": "A", "Q3KummerDescentSpike": "A", "Q3KummerCubeIdent": "A", "Q3Mu9Completeness": "A", "Q3KummerYPow": "A", "Q3KummerPiSplit": "A", "Q3TateCurveL9": "A", "Q3Mu9ThetaGroup": "A", "Q3Mu9Rigidity": "A", "Q3Mu9TmzBridge": "A", "Q3KummerDualityReal": "B", "Q3WildRamFiltrationReal": "B", "Q3RatEmbed": "A", "Q3Etale9TwoDir": "A", "Q3Mu27DescentSpike": "A", "Q3HasseArfReal": "B", "Q3ArtinConductorReal": "B", "Q3NormFiltrationSpike": "B", "Q3CubeQuotientReal": "B", "Q3TowerDifferentReal": "B", "Q3TraceDifferentReal": "B", "Q3HerbrandReal": "B", "Q3GenLowerFiltrationReal": "B", "Q3ResidueFieldReal": "B", "Q3GradedNormBreak": "B", "Q3LocalReciprocityReal": "B", "Q3ReciprocityCokernelReal": "B", "Q3ReciprocityGalReal": "B", "Q3CokernelObjectReal": "B", "Q3DifferentValuation": "B", "Q3DifferentIdeal": "B", "Q3Codifferent": "B", "Q3ValuationReal": "B", "Q3NormSurjGraded": "B", "Q3NormSurjPeelBase": "B", "Q3HasseArfIntegral": "B", "Q3NormSurjPeelGeneral": "B", "Q3TemperedEtDensity": "A", "Q3TemperedThetaClassL9": "A", "Q3NormSurjSuccApprox": "B", "Q3FractionalCodifferent": "B", "TripodKummerMu3": "A",
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
