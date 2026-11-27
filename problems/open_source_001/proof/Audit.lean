import Main
import Nonsmooth
import Nonsmooth.AEDirectionalNorm
import Nonsmooth.AERankControlledSelection
import Nonsmooth.ActualBodyLocalCertificate
import Nonsmooth.ActualCyclicPeak
import Nonsmooth.ActualDyadicPeak
import Nonsmooth.ActualFullDimensionalConePolicy
import Nonsmooth.ActualNestedCircularPolicy
import Nonsmooth.ActualOrthogonalPotentialMarginal
import Nonsmooth.AdaptedDirection
import Nonsmooth.AdaptiveBlockLegality
import Nonsmooth.AdaptiveBlockPolicy
import Nonsmooth.AdaptiveCyclicPolicy
import Nonsmooth.AdaptiveIsometry
import Nonsmooth.AdaptiveOutput
import Nonsmooth.AdaptiveResponse
import Nonsmooth.AffineBallConstraints
import Nonsmooth.AffineGaussianPolytopeConcentration
import Nonsmooth.AffineObservationCDF
import Nonsmooth.AffineObservationPosterior
import Nonsmooth.AffinePolytopeCovariance
import Nonsmooth.AffinePolytopeProjectionRank
import Nonsmooth.AffineProjectionRank
import Nonsmooth.AffineProjectionShift
import Nonsmooth.AllDimensionalPolytopeRank
import Nonsmooth.AllStepGaussianCovariance
import Nonsmooth.AllStepGaussianEnergy
import Nonsmooth.AnchoredCircularPeak
import Nonsmooth.ArcEnergy
import Nonsmooth.AspectConeParameters
import Nonsmooth.AtomlessCDFEntropy
import Nonsmooth.AugmentedSupport
import Nonsmooth.BallPolytopePotentialClass
import Nonsmooth.BallProjection
import Nonsmooth.Basic
import Nonsmooth.BestValueRecord
import Nonsmooth.BodyFallbackMap
import Nonsmooth.BodyPullbackGeometry
import Nonsmooth.BodyTreeInitialSubset
import Nonsmooth.C2GaussianConcentration
import Nonsmooth.C2GaussianCovariance
import Nonsmooth.C2GaussianPlaneBase
import Nonsmooth.C2GaussianRegularImages
import Nonsmooth.C2GaussianUnitMarginal
import Nonsmooth.C2PotentialIsometryPullback
import Nonsmooth.C2PotentialPlaneRegularity
import Nonsmooth.C2ProjectionImage
import Nonsmooth.C2StrongQuadraticPotential
import Nonsmooth.CenteredBodyTranslation
import Nonsmooth.CentroidInterior
import Nonsmooth.Chord
import Nonsmooth.CircularConeGeometry
import Nonsmooth.CircularConeSector
import Nonsmooth.CircularGeometryState
import Nonsmooth.CircularNeighborLiftGeometry
import Nonsmooth.CircularQueryGrid
import Nonsmooth.CircularWideConePolicy
import Nonsmooth.CompactIntegration
import Nonsmooth.ComparisonHistoryPolicy
import Nonsmooth.CompleteGaussianHardness
import Nonsmooth.ConditionalEventBayes
import Nonsmooth.ConditionalEventKernel
import Nonsmooth.ConditionalEventMoments
import Nonsmooth.ConditionalImage
import Nonsmooth.ConditionalJointImage
import Nonsmooth.ConditionalLower
import Nonsmooth.ConditionalMean
import Nonsmooth.ConditionalMoments
import Nonsmooth.ConditionalReencoding
import Nonsmooth.ConditionalRowCovarianceDense
import Nonsmooth.ConditionalSupportUpdate
import Nonsmooth.ConditionedProducts
import Nonsmooth.ConditioningAEExhaustion
import Nonsmooth.ConditioningExhaustion
import Nonsmooth.ConditioningProbability
import Nonsmooth.ConeCapGeometry
import Nonsmooth.ConeLiftCoefficient
import Nonsmooth.ConeSectionLift
import Nonsmooth.ConstantObservationAE
import Nonsmooth.ContinuousPolicy
import Nonsmooth.ContinuousProtocol
import Nonsmooth.ContinuousRank
import Nonsmooth.ContinuousUpdate
import Nonsmooth.ConvexCapVolume
import Nonsmooth.ConvexPotentialTail
import Nonsmooth.ConvexQuadraticGradient
import Nonsmooth.CoordinateHessianGrowth
import Nonsmooth.CountableBodyTree
import Nonsmooth.CountableProtocol
import Nonsmooth.CovarianceExhaustion
import Nonsmooth.CyclicPeakBracket
import Nonsmooth.CyclicPeakLegality
import Nonsmooth.DerivativeEnergy
import Nonsmooth.DeterminedProjectionShift
import Nonsmooth.DeterminedScalarPosterior
import Nonsmooth.DimensionCircularPrecision
import Nonsmooth.DirectionalResidual
import Nonsmooth.DiscreteBodyCut
import Nonsmooth.DiscreteBodyVolumeCut
import Nonsmooth.DiscreteConeReadout
import Nonsmooth.DominatedPotentialContinuity
import Nonsmooth.DominatedSliceNoSpike
import Nonsmooth.DyadicPeakLegality
import Nonsmooth.DyadicPeakSearch
import Nonsmooth.Embedding
import Nonsmooth.EvaluatedLocalizationBudget
import Nonsmooth.EvaluatedLocalizationLegality
import Nonsmooth.EvaluatedLocalizationPolicy
import Nonsmooth.EventBarycenter
import Nonsmooth.EventComplement
import Nonsmooth.FiniteComparisonCone
import Nonsmooth.FiniteFirstIntegral
import Nonsmooth.FiniteObservationIntegral
import Nonsmooth.FiniteProductKernel
import Nonsmooth.FiniteSampling
import Nonsmooth.FiniteSupport
import Nonsmooth.FirstOrder
import Nonsmooth.FixedBudgetPadding
import Nonsmooth.FixedProjection
import Nonsmooth.FrameGeometry
import Nonsmooth.FrameStep
import Nonsmooth.FullLineCovarianceBrascampLieb
import Nonsmooth.GaussianAdaptiveGap
import Nonsmooth.GaussianAdaptiveRows
import Nonsmooth.GaussianAdaptiveSquare
import Nonsmooth.GaussianAmbientRowLaw
import Nonsmooth.GaussianAxialCap
import Nonsmooth.GaussianAxialSlab
import Nonsmooth.GaussianAxisDecomposition
import Nonsmooth.GaussianBaseCovarianceReduction
import Nonsmooth.GaussianCapPerpendicular
import Nonsmooth.GaussianCapScaling
import Nonsmooth.GaussianCharacteristic
import Nonsmooth.GaussianCombination
import Nonsmooth.GaussianConcentration
import Nonsmooth.GaussianConditionalMeans
import Nonsmooth.GaussianCoordinateIntegration
import Nonsmooth.GaussianDirection
import Nonsmooth.GaussianEnergy
import Nonsmooth.GaussianEnergyOnlyReduction
import Nonsmooth.GaussianEventSlices
import Nonsmooth.GaussianExponential
import Nonsmooth.GaussianFirstLogEnergy
import Nonsmooth.GaussianFirstMeanFormula
import Nonsmooth.GaussianFirstObservation
import Nonsmooth.GaussianFirstQuery
import Nonsmooth.GaussianFourth
import Nonsmooth.GaussianHalfspaceCovariance
import Nonsmooth.GaussianHalfspaceMean
import Nonsmooth.GaussianHardnessReduction
import Nonsmooth.GaussianInitialCovariance
import Nonsmooth.GaussianIntervalMGF
import Nonsmooth.GaussianLeftInterval
import Nonsmooth.GaussianLinearMGF
import Nonsmooth.GaussianLinearTail
import Nonsmooth.GaussianLoserEnergy
import Nonsmooth.GaussianMaximumMoment
import Nonsmooth.GaussianNegativeCap
import Nonsmooth.GaussianNegativeSlab
import Nonsmooth.GaussianOrthogonalComponents
import Nonsmooth.GaussianOrthogonalCoordinateLaw
import Nonsmooth.GaussianOutputCriterion
import Nonsmooth.GaussianPairPotentialDensity
import Nonsmooth.GaussianPlaneCoordinates
import Nonsmooth.GaussianPolar
import Nonsmooth.GaussianPolynomialEnvelope
import Nonsmooth.GaussianPolytopeActualEnergy
import Nonsmooth.GaussianPolytopeAffinePosterior
import Nonsmooth.GaussianPolytopeConcentration
import Nonsmooth.GaussianPolytopeCovariance
import Nonsmooth.GaussianPolytopeCuts
import Nonsmooth.GaussianPolytopeEnergy
import Nonsmooth.GaussianPolytopeLoserModel
import Nonsmooth.GaussianPolytopeModel
import Nonsmooth.GaussianPolytopeMoments
import Nonsmooth.GaussianPolytopeParametricUpdate
import Nonsmooth.GaussianPolytopePosterior
import Nonsmooth.GaussianPolytopeProjectionClosure
import Nonsmooth.GaussianPolytopeProjectionRank
import Nonsmooth.GaussianPolytopeRowConcentration
import Nonsmooth.GaussianPolytopeRowProjectionRank
import Nonsmooth.GaussianPolytopeScalar
import Nonsmooth.GaussianPolytopeScaling
import Nonsmooth.GaussianPolytopeSelectionClosure
import Nonsmooth.GaussianPolytopeSlices
import Nonsmooth.GaussianPolytopeSubspace
import Nonsmooth.GaussianPolytopeWeights
import Nonsmooth.GaussianPolytopeWinnerModel
import Nonsmooth.GaussianPosteriorEnergy
import Nonsmooth.GaussianPosteriorHardness
import Nonsmooth.GaussianPotentialDensity
import Nonsmooth.GaussianPrior
import Nonsmooth.GaussianPriorIdentity
import Nonsmooth.GaussianProjectionAtoms
import Nonsmooth.GaussianProjectionPosterior
import Nonsmooth.GaussianQuadraticBoundary
import Nonsmooth.GaussianRadialTruncation
import Nonsmooth.GaussianRealMoments
import Nonsmooth.GaussianRowCentering
import Nonsmooth.GaussianRowCovarianceHardness
import Nonsmooth.GaussianRowCovarianceResidual
import Nonsmooth.GaussianRowGeometry
import Nonsmooth.GaussianRowTruncation
import Nonsmooth.GaussianRowsCharacteristic
import Nonsmooth.GaussianScaledSlab
import Nonsmooth.GaussianScaledSlices
import Nonsmooth.GaussianSelectionRank
import Nonsmooth.GaussianSharpMGF
import Nonsmooth.GaussianSingle
import Nonsmooth.GaussianSingleHardness
import Nonsmooth.GaussianSlabCovariance
import Nonsmooth.GaussianSlabKernel
import Nonsmooth.GaussianSlabSelection
import Nonsmooth.GaussianSlabUpdates
import Nonsmooth.GaussianSliceCovariance
import Nonsmooth.GaussianSpectral
import Nonsmooth.GaussianSpectralBridge
import Nonsmooth.GaussianSquareMGF
import Nonsmooth.GaussianSubspaceLaw
import Nonsmooth.GaussianSupportPosterior
import Nonsmooth.GaussianTruncated
import Nonsmooth.GaussianWinnerCovariance
import Nonsmooth.GaussianWinnerMean
import Nonsmooth.GaussianZeroQuery
import Nonsmooth.GeneralBodyNormalization
import Nonsmooth.GeneralBodyProtasov
import Nonsmooth.GeneralBodyVolumeAccuracy
import Nonsmooth.GeneralCDFEntropy
import Nonsmooth.GeneralCDFRank
import Nonsmooth.GeneralEvaluatedLocalization
import Nonsmooth.GeneralGrunbaumCenter
import Nonsmooth.GeneralMaximumEntropy
import Nonsmooth.GeneralMaximumShift
import Nonsmooth.Geometry
import Nonsmooth.GrunbaumApplication
import Nonsmooth.GrunbaumConstantBound
import Nonsmooth.GuardedHalfspaceCut
import Nonsmooth.HalfspaceCutBody
import Nonsmooth.HalfspaceDepthAsymmetry
import Nonsmooth.HalfspacePosteriorShift
import Nonsmooth.HessianConvexity
import Nonsmooth.HistoryPolicy
import Nonsmooth.HistoryReflection
import Nonsmooth.ImportedGeometryBasic
import Nonsmooth.ImportedGeometryBrunnMinkowski
import Nonsmooth.ImportedGeometryDefinitions
import Nonsmooth.ImportedGeometryFinalBridge
import Nonsmooth.ImportedGeometryMain
import Nonsmooth.ImportedGeometryPrekopaLeindler
import Nonsmooth.ImportedGeometryProbabilityCore
import Nonsmooth.ImportedGeometryTruncationConcavity
import Nonsmooth.IndependentCovariance
import Nonsmooth.IndependentInnerProduct
import Nonsmooth.InteriorDepthCenter
import Nonsmooth.IntervalCovarianceBrascampLieb
import Nonsmooth.IntervalDensityLaw
import Nonsmooth.IntervalDensityVariance
import Nonsmooth.IntervalPotentialEvents
import Nonsmooth.IntervalPotentialMGF
import Nonsmooth.IntervalPotentialMoments
import Nonsmooth.KernelCovarianceMeasurability
import Nonsmooth.KernelExponentialJensen
import Nonsmooth.KernelInvariantConsequences
import Nonsmooth.LinearCoordinateCalculus
import Nonsmooth.LinearDepthTransport
import Nonsmooth.LinearPolicyTail
import Nonsmooth.LocalizationBestInvariant
import Nonsmooth.LocalizationBody
import Nonsmooth.LocalizationRetention
import Nonsmooth.LocalizationVolumeAccuracy
import Nonsmooth.LogarithmicVolumeRounds
import Nonsmooth.LowerHalflineExhaustion
import Nonsmooth.MaximalDeterminantBasis
import Nonsmooth.MaximumTailCost
import Nonsmooth.MeasurableSimulation
import Nonsmooth.Minimax
import Nonsmooth.MixedAggregateEnergy
import Nonsmooth.MixedLoserShiftEnergy
import Nonsmooth.MixedProjectionEnergy
import Nonsmooth.MixedRankSelection
import Nonsmooth.MixedSelectionLoserKernel
import Nonsmooth.MixedWinnerRank
import Nonsmooth.NestedCircularDimension
import Nonsmooth.NestedCircularDirection
import Nonsmooth.NestedCircularFinalRay
import Nonsmooth.NestedCircularFullCone
import Nonsmooth.NestedCircularNeighborGeometry
import Nonsmooth.NestedCircularPairCertificate
import Nonsmooth.NestedCircularPath
import Nonsmooth.NestedCircularStepData
import Nonsmooth.NetOperator
import Nonsmooth.NoSpikeLevelMass
import Nonsmooth.NoSpikeProbability
import Nonsmooth.NoSpikeSmooth
import Nonsmooth.NormalizedBodyCutPolicy
import Nonsmooth.NormalizedBodyVolumeCut
import Nonsmooth.NormalizedConeParameters
import Nonsmooth.NormalizedLocalCertificate
import Nonsmooth.ObservationEventStability
import Nonsmooth.ObservedBayes
import Nonsmooth.ObservedKernel
import Nonsmooth.OffsetGaussianMomentRegularity
import Nonsmooth.OracleSimulation
import Nonsmooth.OrthogonalConeLift
import Nonsmooth.OrthogonalCoordinateBounds
import Nonsmooth.OrthogonalCoordinateCurvature
import Nonsmooth.OrthogonalHaar
import Nonsmooth.OrthogonalMarginalClosure
import Nonsmooth.OrthogonalMeanEnergy
import Nonsmooth.OrthogonalPairReduction
import Nonsmooth.OrthogonalPlaneBounds
import Nonsmooth.OrthogonalSphere
import Nonsmooth.OrthonormalBallSandwich
import Nonsmooth.ParameterizedMarginalCurvature
import Nonsmooth.ParametricEventKernel
import Nonsmooth.ParametricPotentialExpectation
import Nonsmooth.ParametricPotentialMoment
import Nonsmooth.ParametricRegressionIdentities
import Nonsmooth.ParametricSelection
import Nonsmooth.ParametricSupportEnergy
import Nonsmooth.PeakValueMonotonicity
import Nonsmooth.PerpendicularReflection
import Nonsmooth.PiEstimate
import Nonsmooth.PlaneRotation
import Nonsmooth.PlaneSliceBounds
import Nonsmooth.PlaneSliceData
import Nonsmooth.PolicyGaussianCovariance
import Nonsmooth.PolicyRecursiveMean
import Nonsmooth.PolicyResponseEncoding
import Nonsmooth.PolynomialAspectBudget
import Nonsmooth.PolynomialDensityMoments
import Nonsmooth.PolynomialVectorDensityMoments
import Nonsmooth.PosteriorAggregateEnergy
import Nonsmooth.PosteriorBudget
import Nonsmooth.PosteriorCrossMoments
import Nonsmooth.PosteriorDirectionalBound
import Nonsmooth.PosteriorEnergy
import Nonsmooth.PosteriorEnergyReencoding
import Nonsmooth.PosteriorKnownFunctions
import Nonsmooth.PosteriorMeanScaling
import Nonsmooth.PosteriorRowMoments
import Nonsmooth.PosteriorSupportTail
import Nonsmooth.PotentialJointDensity
import Nonsmooth.PotentialJointSwap
import Nonsmooth.PotentialMomentDerivative
import Nonsmooth.PotentialPartitionDerivatives
import Nonsmooth.PotentialSliceKernel
import Nonsmooth.PrimitiveStrongSliceFamily
import Nonsmooth.PriorRisk
import Nonsmooth.ProductMarginals
import Nonsmooth.ProductPosteriorAtoms
import Nonsmooth.ProductProbability
import Nonsmooth.ProjectedPolicy
import Nonsmooth.ProjectionPosteriorDirection
import Nonsmooth.ProjectionRankApproximation
import Nonsmooth.ProjectionSlice
import Nonsmooth.ProtasovTransfer
import Nonsmooth.ProtasovVolumeCertificate
import Nonsmooth.QuadraticEnvelopeClosure
import Nonsmooth.QuadraticMarginalEnvelope
import Nonsmooth.QuadraticSliceConstraints
import Nonsmooth.QuadraticSliceGrowth
import Nonsmooth.QuadraticSoftNoSpike
import Nonsmooth.QuadraticSoftPotentialBounds
import Nonsmooth.QuarterDepthNormalization
import Nonsmooth.QueryCompletion
import Nonsmooth.QueryOutputValue
import Nonsmooth.Radial
import Nonsmooth.RadialAveraging
import Nonsmooth.RadialIndependence
import Nonsmooth.RadialQuadraticCalculus
import Nonsmooth.RankBoundLimit
import Nonsmooth.RankControlledSelection
import Nonsmooth.RankMoments
import Nonsmooth.RankQuantileMoment
import Nonsmooth.RankTailEntropy
import Nonsmooth.RealDensityEventMass
import Nonsmooth.RealDensityLaw
import Nonsmooth.RecursiveBeliefDisintegration
import Nonsmooth.RecursiveConeCertificate
import Nonsmooth.RecursiveGaussianConsequences
import Nonsmooth.RecursiveGaussianCovariance
import Nonsmooth.RecursiveGaussianMeanEnergy
import Nonsmooth.RecursiveGaussianStepEnergy
import Nonsmooth.RecursiveIncrementIntegral
import Nonsmooth.RecursiveMeanMoments
import Nonsmooth.RecursiveResponseChain
import Nonsmooth.RecursiveSupportBelief
import Nonsmooth.RecursiveSupportResponse
import Nonsmooth.ReflectionObservation
import Nonsmooth.ReflectionVariance
import Nonsmooth.RegressionConcentration
import Nonsmooth.RegularImageMoments
import Nonsmooth.RegularJointPosterior
import Nonsmooth.RegularMarginalConcentration
import Nonsmooth.RegularProjectionNoSpike
import Nonsmooth.RegularSliceCurvature
import Nonsmooth.RegularSliceSelection
import Nonsmooth.RegularStrongSliceFamily
import Nonsmooth.RegularTwoDimensionalNoSpike
import Nonsmooth.RegularVectorConcentration
import Nonsmooth.RegularVectorCoordinateFamily
import Nonsmooth.RegularVectorEnergy
import Nonsmooth.RegularVectorMoments
import Nonsmooth.RegularVectorNoSpike
import Nonsmooth.RegularVectorSupportEnergy
import Nonsmooth.ResponseHistoryAugmentation
import Nonsmooth.ResponseHistoryEncoding
import Nonsmooth.RotationalConditionalMean
import Nonsmooth.RotationalCovariance
import Nonsmooth.RotationalUniqueness
import Nonsmooth.ScalarC2PotentialConcentration
import Nonsmooth.ScalarConcentrationRank
import Nonsmooth.ScalarMGFTails
import Nonsmooth.ScalarPairConcentration
import Nonsmooth.Scales
import Nonsmooth.ScoreCovarianceEvaluation
import Nonsmooth.SelectedBlockLegality
import Nonsmooth.SelectedBlockPolicy
import Nonsmooth.SelectedExponentialEnergy
import Nonsmooth.SelectedProjection
import Nonsmooth.SelectedUpdate
import Nonsmooth.SelectionCovarianceCriterion
import Nonsmooth.SelectionDisintegration
import Nonsmooth.SelectionGeometry
import Nonsmooth.SelectionIntegral
import Nonsmooth.SelectionMeasure
import Nonsmooth.SelectionPosterior
import Nonsmooth.ShrinkingCircularRadii
import Nonsmooth.SingleSupport
import Nonsmooth.SliceRegressionCurvature
import Nonsmooth.SoftConditionedSupportEnergy
import Nonsmooth.SoftGaussianDamping
import Nonsmooth.SoftHessianAlgebra
import Nonsmooth.SoftInequalityPotential
import Nonsmooth.SoftInequalityStep
import Nonsmooth.SoftInequalityWeights
import Nonsmooth.SoftPosteriorLimits
import Nonsmooth.SoftProjectionLimit
import Nonsmooth.SoftProjectionRank
import Nonsmooth.SoftSliceDerivatives
import Nonsmooth.SoftSliceGrowthBounds
import Nonsmooth.SoftSliceProperties
import Nonsmooth.SoftSliceRegularity
import Nonsmooth.SoftVectorConcentration
import Nonsmooth.SoftVectorHessianBounds
import Nonsmooth.SoftVectorPotentialCalculus
import Nonsmooth.SoftVectorPotentialClass
import Nonsmooth.SoftWeightCDF
import Nonsmooth.SoftWeightLimits
import Nonsmooth.SoftWeightMGF
import Nonsmooth.SoftWeightedVarianceLimit
import Nonsmooth.SoftplusConvexity
import Nonsmooth.SoftplusDerivatives
import Nonsmooth.SoftplusVectorDerivatives
import Nonsmooth.SpanningGaussianPotentialLaw
import Nonsmooth.SpanningProjectionRank
import Nonsmooth.SphereNet
import Nonsmooth.SphereRisk
import Nonsmooth.SphericalFrame
import Nonsmooth.SphericalLaw
import Nonsmooth.StaticGaussianPolytopeEnergy
import Nonsmooth.SteinEnergy
import Nonsmooth.SteinPenalty
import Nonsmooth.StrongCoordinateCovariance
import Nonsmooth.StrongPotentialHalfline
import Nonsmooth.StrongPotentialMGF
import Nonsmooth.StrongPotentialRawMoment
import Nonsmooth.StrongPotentialTails
import Nonsmooth.StrongPotentialTilts
import Nonsmooth.StrongPotentialVariance
import Nonsmooth.StrongScoreVariance
import Nonsmooth.SubspaceCircularFrame
import Nonsmooth.SubspaceCircularGeometry
import Nonsmooth.SubspaceCircularSection
import Nonsmooth.SubspaceConeLift
import Nonsmooth.SuperlevelCrossing
import Nonsmooth.SupportAffineGeometry
import Nonsmooth.SupportAggregateCriterion
import Nonsmooth.SupportCommonComponent
import Nonsmooth.SupportCore
import Nonsmooth.SupportEnergyScaling
import Nonsmooth.SupportGram
import Nonsmooth.SupportLoserShift
import Nonsmooth.SupportMaximumEntropy
import Nonsmooth.SupportNoInformation
import Nonsmooth.SupportObservation
import Nonsmooth.SupportPosteriorIndependence
import Nonsmooth.SupportPosteriorKernel
import Nonsmooth.SupportProjectionRankCriterion
import Nonsmooth.SupportQueryNormalization
import Nonsmooth.SupportSelectionKernel
import Nonsmooth.SupportTranscriptInfo
import Nonsmooth.SupportWinnerRank
import Nonsmooth.SymmetricBodyNormalization
import Nonsmooth.SymmetricConvexCombination
import Nonsmooth.SymmetricCoreDepth
import Nonsmooth.SymmetricHalfspaceMoment
import Nonsmooth.SymmetricIntervalMoment
import Nonsmooth.TiltedMomentCalculus
import Nonsmooth.TruncationMonotonicity
import Nonsmooth.TwoQueryOutwardCone
import Nonsmooth.UniformBodyLocalCertificate
import Nonsmooth.UnitMGFNoSpike
import Nonsmooth.VectorCoordinateCurvature
import Nonsmooth.VectorCoordinateGrowth
import Nonsmooth.VectorCoordinateHessianGrowth
import Nonsmooth.VectorCoordinateMoments
import Nonsmooth.VectorCoordinateSymmetry
import Nonsmooth.VectorGaussianEnvelope
import Nonsmooth.VectorPotentialContinuity
import Nonsmooth.VectorPotentialDifferentiation
import Nonsmooth.VectorPotentialExpectation
import Nonsmooth.VectorPotentialNormalization
import Nonsmooth.VectorScoreCovarianceBound
import Nonsmooth.VolumeContractionIteration
import Nonsmooth.WeightedBayes
import Nonsmooth.WeightedDensityLaw
import Nonsmooth.WeightedExpectation
import Nonsmooth.WeightedJointDisintegration
import Nonsmooth.WeightedLawTransport
import Nonsmooth.WeightedPosteriorKernel
import Nonsmooth.WeightedProductMarginal
import Task003Base
import Task003Integration
import Task003Integration.ProtasovBridge
import Task003Integration.ProtasovCoordinates
import Task003Integration.ProtasovPolicyTransport
import Task003Integration.UnconditionalMain
import Task003Integration.ZhangBridge
import Task003Integration.ZhangHardness
import Task003Integration.ZhangMeasure
import Task003Integration.ZhangMeasureCore
import Task003Integration.ZhangPolicy
import Task003Integration.ZhangScale
import Lean.Util.CollectAxioms

example : Task003.OracleModel.FullJointProfile (1 / 8) :=
  Task003.UnconditionalMain.paper_main_unconditional
example : Task003.LiteratureMain.ZhangLiteratureInput :=
  Task003Integration.zhangLiteratureInput_proved
example : Task003.LiteratureMain.ProtasovLiteratureInput :=
  Task003Integration.protasovLiteratureInput_proved

namespace AuditInfrastructure
open Lean
structure BodyState where
  seen : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}

/-- Independent body traversal, without using Lean's exported axiom cache. -/
partial def visit (env : Environment) (name : Name) : StateM BodyState Unit := do
  if (← get).seen.contains name then return
  modify fun s => { s with seen := s.seen.insert name }
  let some info := env.checked.get.find? name |
    modify fun s => { s with missing := s.missing.insert name }
  let visitExpr (e : Expr) := e.getUsedConstants.forM (visit env)
  match info with
  | .axiomInfo v =>
      modify fun s => { s with axioms := s.axioms.insert name }
      visitExpr v.type
  | .defnInfo v => visitExpr v.type *> visitExpr v.value
  | .thmInfo v => visitExpr v.type *> visitExpr v.value
  | .opaqueInfo v => visitExpr v.type *> visitExpr v.value
  | .quotInfo _ => pure ()
  | .ctorInfo v => visitExpr v.type
  | .recInfo v => visitExpr v.type
  | .inductInfo v => visitExpr v.type *> v.ctors.forM (visit env)
end AuditInfrastructure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectModules : Array Name := #[
    `Main,
    `Nonsmooth,
    `Nonsmooth.AEDirectionalNorm,
    `Nonsmooth.AERankControlledSelection,
    `Nonsmooth.ActualBodyLocalCertificate,
    `Nonsmooth.ActualCyclicPeak,
    `Nonsmooth.ActualDyadicPeak,
    `Nonsmooth.ActualFullDimensionalConePolicy,
    `Nonsmooth.ActualNestedCircularPolicy,
    `Nonsmooth.ActualOrthogonalPotentialMarginal,
    `Nonsmooth.AdaptedDirection,
    `Nonsmooth.AdaptiveBlockLegality,
    `Nonsmooth.AdaptiveBlockPolicy,
    `Nonsmooth.AdaptiveCyclicPolicy,
    `Nonsmooth.AdaptiveIsometry,
    `Nonsmooth.AdaptiveOutput,
    `Nonsmooth.AdaptiveResponse,
    `Nonsmooth.AffineBallConstraints,
    `Nonsmooth.AffineGaussianPolytopeConcentration,
    `Nonsmooth.AffineObservationCDF,
    `Nonsmooth.AffineObservationPosterior,
    `Nonsmooth.AffinePolytopeCovariance,
    `Nonsmooth.AffinePolytopeProjectionRank,
    `Nonsmooth.AffineProjectionRank,
    `Nonsmooth.AffineProjectionShift,
    `Nonsmooth.AllDimensionalPolytopeRank,
    `Nonsmooth.AllStepGaussianCovariance,
    `Nonsmooth.AllStepGaussianEnergy,
    `Nonsmooth.AnchoredCircularPeak,
    `Nonsmooth.ArcEnergy,
    `Nonsmooth.AspectConeParameters,
    `Nonsmooth.AtomlessCDFEntropy,
    `Nonsmooth.AugmentedSupport,
    `Nonsmooth.BallPolytopePotentialClass,
    `Nonsmooth.BallProjection,
    `Nonsmooth.Basic,
    `Nonsmooth.BestValueRecord,
    `Nonsmooth.BodyFallbackMap,
    `Nonsmooth.BodyPullbackGeometry,
    `Nonsmooth.BodyTreeInitialSubset,
    `Nonsmooth.C2GaussianConcentration,
    `Nonsmooth.C2GaussianCovariance,
    `Nonsmooth.C2GaussianPlaneBase,
    `Nonsmooth.C2GaussianRegularImages,
    `Nonsmooth.C2GaussianUnitMarginal,
    `Nonsmooth.C2PotentialIsometryPullback,
    `Nonsmooth.C2PotentialPlaneRegularity,
    `Nonsmooth.C2ProjectionImage,
    `Nonsmooth.C2StrongQuadraticPotential,
    `Nonsmooth.CenteredBodyTranslation,
    `Nonsmooth.CentroidInterior,
    `Nonsmooth.Chord,
    `Nonsmooth.CircularConeGeometry,
    `Nonsmooth.CircularConeSector,
    `Nonsmooth.CircularGeometryState,
    `Nonsmooth.CircularNeighborLiftGeometry,
    `Nonsmooth.CircularQueryGrid,
    `Nonsmooth.CircularWideConePolicy,
    `Nonsmooth.CompactIntegration,
    `Nonsmooth.ComparisonHistoryPolicy,
    `Nonsmooth.CompleteGaussianHardness,
    `Nonsmooth.ConditionalEventBayes,
    `Nonsmooth.ConditionalEventKernel,
    `Nonsmooth.ConditionalEventMoments,
    `Nonsmooth.ConditionalImage,
    `Nonsmooth.ConditionalJointImage,
    `Nonsmooth.ConditionalLower,
    `Nonsmooth.ConditionalMean,
    `Nonsmooth.ConditionalMoments,
    `Nonsmooth.ConditionalReencoding,
    `Nonsmooth.ConditionalRowCovarianceDense,
    `Nonsmooth.ConditionalSupportUpdate,
    `Nonsmooth.ConditionedProducts,
    `Nonsmooth.ConditioningAEExhaustion,
    `Nonsmooth.ConditioningExhaustion,
    `Nonsmooth.ConditioningProbability,
    `Nonsmooth.ConeCapGeometry,
    `Nonsmooth.ConeLiftCoefficient,
    `Nonsmooth.ConeSectionLift,
    `Nonsmooth.ConstantObservationAE,
    `Nonsmooth.ContinuousPolicy,
    `Nonsmooth.ContinuousProtocol,
    `Nonsmooth.ContinuousRank,
    `Nonsmooth.ContinuousUpdate,
    `Nonsmooth.ConvexCapVolume,
    `Nonsmooth.ConvexPotentialTail,
    `Nonsmooth.ConvexQuadraticGradient,
    `Nonsmooth.CoordinateHessianGrowth,
    `Nonsmooth.CountableBodyTree,
    `Nonsmooth.CountableProtocol,
    `Nonsmooth.CovarianceExhaustion,
    `Nonsmooth.CyclicPeakBracket,
    `Nonsmooth.CyclicPeakLegality,
    `Nonsmooth.DerivativeEnergy,
    `Nonsmooth.DeterminedProjectionShift,
    `Nonsmooth.DeterminedScalarPosterior,
    `Nonsmooth.DimensionCircularPrecision,
    `Nonsmooth.DirectionalResidual,
    `Nonsmooth.DiscreteBodyCut,
    `Nonsmooth.DiscreteBodyVolumeCut,
    `Nonsmooth.DiscreteConeReadout,
    `Nonsmooth.DominatedPotentialContinuity,
    `Nonsmooth.DominatedSliceNoSpike,
    `Nonsmooth.DyadicPeakLegality,
    `Nonsmooth.DyadicPeakSearch,
    `Nonsmooth.Embedding,
    `Nonsmooth.EvaluatedLocalizationBudget,
    `Nonsmooth.EvaluatedLocalizationLegality,
    `Nonsmooth.EvaluatedLocalizationPolicy,
    `Nonsmooth.EventBarycenter,
    `Nonsmooth.EventComplement,
    `Nonsmooth.FiniteComparisonCone,
    `Nonsmooth.FiniteFirstIntegral,
    `Nonsmooth.FiniteObservationIntegral,
    `Nonsmooth.FiniteProductKernel,
    `Nonsmooth.FiniteSampling,
    `Nonsmooth.FiniteSupport,
    `Nonsmooth.FirstOrder,
    `Nonsmooth.FixedBudgetPadding,
    `Nonsmooth.FixedProjection,
    `Nonsmooth.FrameGeometry,
    `Nonsmooth.FrameStep,
    `Nonsmooth.FullLineCovarianceBrascampLieb,
    `Nonsmooth.GaussianAdaptiveGap,
    `Nonsmooth.GaussianAdaptiveRows,
    `Nonsmooth.GaussianAdaptiveSquare,
    `Nonsmooth.GaussianAmbientRowLaw,
    `Nonsmooth.GaussianAxialCap,
    `Nonsmooth.GaussianAxialSlab,
    `Nonsmooth.GaussianAxisDecomposition,
    `Nonsmooth.GaussianBaseCovarianceReduction,
    `Nonsmooth.GaussianCapPerpendicular,
    `Nonsmooth.GaussianCapScaling,
    `Nonsmooth.GaussianCharacteristic,
    `Nonsmooth.GaussianCombination,
    `Nonsmooth.GaussianConcentration,
    `Nonsmooth.GaussianConditionalMeans,
    `Nonsmooth.GaussianCoordinateIntegration,
    `Nonsmooth.GaussianDirection,
    `Nonsmooth.GaussianEnergy,
    `Nonsmooth.GaussianEnergyOnlyReduction,
    `Nonsmooth.GaussianEventSlices,
    `Nonsmooth.GaussianExponential,
    `Nonsmooth.GaussianFirstLogEnergy,
    `Nonsmooth.GaussianFirstMeanFormula,
    `Nonsmooth.GaussianFirstObservation,
    `Nonsmooth.GaussianFirstQuery,
    `Nonsmooth.GaussianFourth,
    `Nonsmooth.GaussianHalfspaceCovariance,
    `Nonsmooth.GaussianHalfspaceMean,
    `Nonsmooth.GaussianHardnessReduction,
    `Nonsmooth.GaussianInitialCovariance,
    `Nonsmooth.GaussianIntervalMGF,
    `Nonsmooth.GaussianLeftInterval,
    `Nonsmooth.GaussianLinearMGF,
    `Nonsmooth.GaussianLinearTail,
    `Nonsmooth.GaussianLoserEnergy,
    `Nonsmooth.GaussianMaximumMoment,
    `Nonsmooth.GaussianNegativeCap,
    `Nonsmooth.GaussianNegativeSlab,
    `Nonsmooth.GaussianOrthogonalComponents,
    `Nonsmooth.GaussianOrthogonalCoordinateLaw,
    `Nonsmooth.GaussianOutputCriterion,
    `Nonsmooth.GaussianPairPotentialDensity,
    `Nonsmooth.GaussianPlaneCoordinates,
    `Nonsmooth.GaussianPolar,
    `Nonsmooth.GaussianPolynomialEnvelope,
    `Nonsmooth.GaussianPolytopeActualEnergy,
    `Nonsmooth.GaussianPolytopeAffinePosterior,
    `Nonsmooth.GaussianPolytopeConcentration,
    `Nonsmooth.GaussianPolytopeCovariance,
    `Nonsmooth.GaussianPolytopeCuts,
    `Nonsmooth.GaussianPolytopeEnergy,
    `Nonsmooth.GaussianPolytopeLoserModel,
    `Nonsmooth.GaussianPolytopeModel,
    `Nonsmooth.GaussianPolytopeMoments,
    `Nonsmooth.GaussianPolytopeParametricUpdate,
    `Nonsmooth.GaussianPolytopePosterior,
    `Nonsmooth.GaussianPolytopeProjectionClosure,
    `Nonsmooth.GaussianPolytopeProjectionRank,
    `Nonsmooth.GaussianPolytopeRowConcentration,
    `Nonsmooth.GaussianPolytopeRowProjectionRank,
    `Nonsmooth.GaussianPolytopeScalar,
    `Nonsmooth.GaussianPolytopeScaling,
    `Nonsmooth.GaussianPolytopeSelectionClosure,
    `Nonsmooth.GaussianPolytopeSlices,
    `Nonsmooth.GaussianPolytopeSubspace,
    `Nonsmooth.GaussianPolytopeWeights,
    `Nonsmooth.GaussianPolytopeWinnerModel,
    `Nonsmooth.GaussianPosteriorEnergy,
    `Nonsmooth.GaussianPosteriorHardness,
    `Nonsmooth.GaussianPotentialDensity,
    `Nonsmooth.GaussianPrior,
    `Nonsmooth.GaussianPriorIdentity,
    `Nonsmooth.GaussianProjectionAtoms,
    `Nonsmooth.GaussianProjectionPosterior,
    `Nonsmooth.GaussianQuadraticBoundary,
    `Nonsmooth.GaussianRadialTruncation,
    `Nonsmooth.GaussianRealMoments,
    `Nonsmooth.GaussianRowCentering,
    `Nonsmooth.GaussianRowCovarianceHardness,
    `Nonsmooth.GaussianRowCovarianceResidual,
    `Nonsmooth.GaussianRowGeometry,
    `Nonsmooth.GaussianRowTruncation,
    `Nonsmooth.GaussianRowsCharacteristic,
    `Nonsmooth.GaussianScaledSlab,
    `Nonsmooth.GaussianScaledSlices,
    `Nonsmooth.GaussianSelectionRank,
    `Nonsmooth.GaussianSharpMGF,
    `Nonsmooth.GaussianSingle,
    `Nonsmooth.GaussianSingleHardness,
    `Nonsmooth.GaussianSlabCovariance,
    `Nonsmooth.GaussianSlabKernel,
    `Nonsmooth.GaussianSlabSelection,
    `Nonsmooth.GaussianSlabUpdates,
    `Nonsmooth.GaussianSliceCovariance,
    `Nonsmooth.GaussianSpectral,
    `Nonsmooth.GaussianSpectralBridge,
    `Nonsmooth.GaussianSquareMGF,
    `Nonsmooth.GaussianSubspaceLaw,
    `Nonsmooth.GaussianSupportPosterior,
    `Nonsmooth.GaussianTruncated,
    `Nonsmooth.GaussianWinnerCovariance,
    `Nonsmooth.GaussianWinnerMean,
    `Nonsmooth.GaussianZeroQuery,
    `Nonsmooth.GeneralBodyNormalization,
    `Nonsmooth.GeneralBodyProtasov,
    `Nonsmooth.GeneralBodyVolumeAccuracy,
    `Nonsmooth.GeneralCDFEntropy,
    `Nonsmooth.GeneralCDFRank,
    `Nonsmooth.GeneralEvaluatedLocalization,
    `Nonsmooth.GeneralGrunbaumCenter,
    `Nonsmooth.GeneralMaximumEntropy,
    `Nonsmooth.GeneralMaximumShift,
    `Nonsmooth.Geometry,
    `Nonsmooth.GrunbaumApplication,
    `Nonsmooth.GrunbaumConstantBound,
    `Nonsmooth.GuardedHalfspaceCut,
    `Nonsmooth.HalfspaceCutBody,
    `Nonsmooth.HalfspaceDepthAsymmetry,
    `Nonsmooth.HalfspacePosteriorShift,
    `Nonsmooth.HessianConvexity,
    `Nonsmooth.HistoryPolicy,
    `Nonsmooth.HistoryReflection,
    `Nonsmooth.ImportedGeometryBasic,
    `Nonsmooth.ImportedGeometryBrunnMinkowski,
    `Nonsmooth.ImportedGeometryDefinitions,
    `Nonsmooth.ImportedGeometryFinalBridge,
    `Nonsmooth.ImportedGeometryMain,
    `Nonsmooth.ImportedGeometryPrekopaLeindler,
    `Nonsmooth.ImportedGeometryProbabilityCore,
    `Nonsmooth.ImportedGeometryTruncationConcavity,
    `Nonsmooth.IndependentCovariance,
    `Nonsmooth.IndependentInnerProduct,
    `Nonsmooth.InteriorDepthCenter,
    `Nonsmooth.IntervalCovarianceBrascampLieb,
    `Nonsmooth.IntervalDensityLaw,
    `Nonsmooth.IntervalDensityVariance,
    `Nonsmooth.IntervalPotentialEvents,
    `Nonsmooth.IntervalPotentialMGF,
    `Nonsmooth.IntervalPotentialMoments,
    `Nonsmooth.KernelCovarianceMeasurability,
    `Nonsmooth.KernelExponentialJensen,
    `Nonsmooth.KernelInvariantConsequences,
    `Nonsmooth.LinearCoordinateCalculus,
    `Nonsmooth.LinearDepthTransport,
    `Nonsmooth.LinearPolicyTail,
    `Nonsmooth.LocalizationBestInvariant,
    `Nonsmooth.LocalizationBody,
    `Nonsmooth.LocalizationRetention,
    `Nonsmooth.LocalizationVolumeAccuracy,
    `Nonsmooth.LogarithmicVolumeRounds,
    `Nonsmooth.LowerHalflineExhaustion,
    `Nonsmooth.MaximalDeterminantBasis,
    `Nonsmooth.MaximumTailCost,
    `Nonsmooth.MeasurableSimulation,
    `Nonsmooth.Minimax,
    `Nonsmooth.MixedAggregateEnergy,
    `Nonsmooth.MixedLoserShiftEnergy,
    `Nonsmooth.MixedProjectionEnergy,
    `Nonsmooth.MixedRankSelection,
    `Nonsmooth.MixedSelectionLoserKernel,
    `Nonsmooth.MixedWinnerRank,
    `Nonsmooth.NestedCircularDimension,
    `Nonsmooth.NestedCircularDirection,
    `Nonsmooth.NestedCircularFinalRay,
    `Nonsmooth.NestedCircularFullCone,
    `Nonsmooth.NestedCircularNeighborGeometry,
    `Nonsmooth.NestedCircularPairCertificate,
    `Nonsmooth.NestedCircularPath,
    `Nonsmooth.NestedCircularStepData,
    `Nonsmooth.NetOperator,
    `Nonsmooth.NoSpikeLevelMass,
    `Nonsmooth.NoSpikeProbability,
    `Nonsmooth.NoSpikeSmooth,
    `Nonsmooth.NormalizedBodyCutPolicy,
    `Nonsmooth.NormalizedBodyVolumeCut,
    `Nonsmooth.NormalizedConeParameters,
    `Nonsmooth.NormalizedLocalCertificate,
    `Nonsmooth.ObservationEventStability,
    `Nonsmooth.ObservedBayes,
    `Nonsmooth.ObservedKernel,
    `Nonsmooth.OffsetGaussianMomentRegularity,
    `Nonsmooth.OracleSimulation,
    `Nonsmooth.OrthogonalConeLift,
    `Nonsmooth.OrthogonalCoordinateBounds,
    `Nonsmooth.OrthogonalCoordinateCurvature,
    `Nonsmooth.OrthogonalHaar,
    `Nonsmooth.OrthogonalMarginalClosure,
    `Nonsmooth.OrthogonalMeanEnergy,
    `Nonsmooth.OrthogonalPairReduction,
    `Nonsmooth.OrthogonalPlaneBounds,
    `Nonsmooth.OrthogonalSphere,
    `Nonsmooth.OrthonormalBallSandwich,
    `Nonsmooth.ParameterizedMarginalCurvature,
    `Nonsmooth.ParametricEventKernel,
    `Nonsmooth.ParametricPotentialExpectation,
    `Nonsmooth.ParametricPotentialMoment,
    `Nonsmooth.ParametricRegressionIdentities,
    `Nonsmooth.ParametricSelection,
    `Nonsmooth.ParametricSupportEnergy,
    `Nonsmooth.PeakValueMonotonicity,
    `Nonsmooth.PerpendicularReflection,
    `Nonsmooth.PiEstimate,
    `Nonsmooth.PlaneRotation,
    `Nonsmooth.PlaneSliceBounds,
    `Nonsmooth.PlaneSliceData,
    `Nonsmooth.PolicyGaussianCovariance,
    `Nonsmooth.PolicyRecursiveMean,
    `Nonsmooth.PolicyResponseEncoding,
    `Nonsmooth.PolynomialAspectBudget,
    `Nonsmooth.PolynomialDensityMoments,
    `Nonsmooth.PolynomialVectorDensityMoments,
    `Nonsmooth.PosteriorAggregateEnergy,
    `Nonsmooth.PosteriorBudget,
    `Nonsmooth.PosteriorCrossMoments,
    `Nonsmooth.PosteriorDirectionalBound,
    `Nonsmooth.PosteriorEnergy,
    `Nonsmooth.PosteriorEnergyReencoding,
    `Nonsmooth.PosteriorKnownFunctions,
    `Nonsmooth.PosteriorMeanScaling,
    `Nonsmooth.PosteriorRowMoments,
    `Nonsmooth.PosteriorSupportTail,
    `Nonsmooth.PotentialJointDensity,
    `Nonsmooth.PotentialJointSwap,
    `Nonsmooth.PotentialMomentDerivative,
    `Nonsmooth.PotentialPartitionDerivatives,
    `Nonsmooth.PotentialSliceKernel,
    `Nonsmooth.PrimitiveStrongSliceFamily,
    `Nonsmooth.PriorRisk,
    `Nonsmooth.ProductMarginals,
    `Nonsmooth.ProductPosteriorAtoms,
    `Nonsmooth.ProductProbability,
    `Nonsmooth.ProjectedPolicy,
    `Nonsmooth.ProjectionPosteriorDirection,
    `Nonsmooth.ProjectionRankApproximation,
    `Nonsmooth.ProjectionSlice,
    `Nonsmooth.ProtasovTransfer,
    `Nonsmooth.ProtasovVolumeCertificate,
    `Nonsmooth.QuadraticEnvelopeClosure,
    `Nonsmooth.QuadraticMarginalEnvelope,
    `Nonsmooth.QuadraticSliceConstraints,
    `Nonsmooth.QuadraticSliceGrowth,
    `Nonsmooth.QuadraticSoftNoSpike,
    `Nonsmooth.QuadraticSoftPotentialBounds,
    `Nonsmooth.QuarterDepthNormalization,
    `Nonsmooth.QueryCompletion,
    `Nonsmooth.QueryOutputValue,
    `Nonsmooth.Radial,
    `Nonsmooth.RadialAveraging,
    `Nonsmooth.RadialIndependence,
    `Nonsmooth.RadialQuadraticCalculus,
    `Nonsmooth.RankBoundLimit,
    `Nonsmooth.RankControlledSelection,
    `Nonsmooth.RankMoments,
    `Nonsmooth.RankQuantileMoment,
    `Nonsmooth.RankTailEntropy,
    `Nonsmooth.RealDensityEventMass,
    `Nonsmooth.RealDensityLaw,
    `Nonsmooth.RecursiveBeliefDisintegration,
    `Nonsmooth.RecursiveConeCertificate,
    `Nonsmooth.RecursiveGaussianConsequences,
    `Nonsmooth.RecursiveGaussianCovariance,
    `Nonsmooth.RecursiveGaussianMeanEnergy,
    `Nonsmooth.RecursiveGaussianStepEnergy,
    `Nonsmooth.RecursiveIncrementIntegral,
    `Nonsmooth.RecursiveMeanMoments,
    `Nonsmooth.RecursiveResponseChain,
    `Nonsmooth.RecursiveSupportBelief,
    `Nonsmooth.RecursiveSupportResponse,
    `Nonsmooth.ReflectionObservation,
    `Nonsmooth.ReflectionVariance,
    `Nonsmooth.RegressionConcentration,
    `Nonsmooth.RegularImageMoments,
    `Nonsmooth.RegularJointPosterior,
    `Nonsmooth.RegularMarginalConcentration,
    `Nonsmooth.RegularProjectionNoSpike,
    `Nonsmooth.RegularSliceCurvature,
    `Nonsmooth.RegularSliceSelection,
    `Nonsmooth.RegularStrongSliceFamily,
    `Nonsmooth.RegularTwoDimensionalNoSpike,
    `Nonsmooth.RegularVectorConcentration,
    `Nonsmooth.RegularVectorCoordinateFamily,
    `Nonsmooth.RegularVectorEnergy,
    `Nonsmooth.RegularVectorMoments,
    `Nonsmooth.RegularVectorNoSpike,
    `Nonsmooth.RegularVectorSupportEnergy,
    `Nonsmooth.ResponseHistoryAugmentation,
    `Nonsmooth.ResponseHistoryEncoding,
    `Nonsmooth.RotationalConditionalMean,
    `Nonsmooth.RotationalCovariance,
    `Nonsmooth.RotationalUniqueness,
    `Nonsmooth.ScalarC2PotentialConcentration,
    `Nonsmooth.ScalarConcentrationRank,
    `Nonsmooth.ScalarMGFTails,
    `Nonsmooth.ScalarPairConcentration,
    `Nonsmooth.Scales,
    `Nonsmooth.ScoreCovarianceEvaluation,
    `Nonsmooth.SelectedBlockLegality,
    `Nonsmooth.SelectedBlockPolicy,
    `Nonsmooth.SelectedExponentialEnergy,
    `Nonsmooth.SelectedProjection,
    `Nonsmooth.SelectedUpdate,
    `Nonsmooth.SelectionCovarianceCriterion,
    `Nonsmooth.SelectionDisintegration,
    `Nonsmooth.SelectionGeometry,
    `Nonsmooth.SelectionIntegral,
    `Nonsmooth.SelectionMeasure,
    `Nonsmooth.SelectionPosterior,
    `Nonsmooth.ShrinkingCircularRadii,
    `Nonsmooth.SingleSupport,
    `Nonsmooth.SliceRegressionCurvature,
    `Nonsmooth.SoftConditionedSupportEnergy,
    `Nonsmooth.SoftGaussianDamping,
    `Nonsmooth.SoftHessianAlgebra,
    `Nonsmooth.SoftInequalityPotential,
    `Nonsmooth.SoftInequalityStep,
    `Nonsmooth.SoftInequalityWeights,
    `Nonsmooth.SoftPosteriorLimits,
    `Nonsmooth.SoftProjectionLimit,
    `Nonsmooth.SoftProjectionRank,
    `Nonsmooth.SoftSliceDerivatives,
    `Nonsmooth.SoftSliceGrowthBounds,
    `Nonsmooth.SoftSliceProperties,
    `Nonsmooth.SoftSliceRegularity,
    `Nonsmooth.SoftVectorConcentration,
    `Nonsmooth.SoftVectorHessianBounds,
    `Nonsmooth.SoftVectorPotentialCalculus,
    `Nonsmooth.SoftVectorPotentialClass,
    `Nonsmooth.SoftWeightCDF,
    `Nonsmooth.SoftWeightLimits,
    `Nonsmooth.SoftWeightMGF,
    `Nonsmooth.SoftWeightedVarianceLimit,
    `Nonsmooth.SoftplusConvexity,
    `Nonsmooth.SoftplusDerivatives,
    `Nonsmooth.SoftplusVectorDerivatives,
    `Nonsmooth.SpanningGaussianPotentialLaw,
    `Nonsmooth.SpanningProjectionRank,
    `Nonsmooth.SphereNet,
    `Nonsmooth.SphereRisk,
    `Nonsmooth.SphericalFrame,
    `Nonsmooth.SphericalLaw,
    `Nonsmooth.StaticGaussianPolytopeEnergy,
    `Nonsmooth.SteinEnergy,
    `Nonsmooth.SteinPenalty,
    `Nonsmooth.StrongCoordinateCovariance,
    `Nonsmooth.StrongPotentialHalfline,
    `Nonsmooth.StrongPotentialMGF,
    `Nonsmooth.StrongPotentialRawMoment,
    `Nonsmooth.StrongPotentialTails,
    `Nonsmooth.StrongPotentialTilts,
    `Nonsmooth.StrongPotentialVariance,
    `Nonsmooth.StrongScoreVariance,
    `Nonsmooth.SubspaceCircularFrame,
    `Nonsmooth.SubspaceCircularGeometry,
    `Nonsmooth.SubspaceCircularSection,
    `Nonsmooth.SubspaceConeLift,
    `Nonsmooth.SuperlevelCrossing,
    `Nonsmooth.SupportAffineGeometry,
    `Nonsmooth.SupportAggregateCriterion,
    `Nonsmooth.SupportCommonComponent,
    `Nonsmooth.SupportCore,
    `Nonsmooth.SupportEnergyScaling,
    `Nonsmooth.SupportGram,
    `Nonsmooth.SupportLoserShift,
    `Nonsmooth.SupportMaximumEntropy,
    `Nonsmooth.SupportNoInformation,
    `Nonsmooth.SupportObservation,
    `Nonsmooth.SupportPosteriorIndependence,
    `Nonsmooth.SupportPosteriorKernel,
    `Nonsmooth.SupportProjectionRankCriterion,
    `Nonsmooth.SupportQueryNormalization,
    `Nonsmooth.SupportSelectionKernel,
    `Nonsmooth.SupportTranscriptInfo,
    `Nonsmooth.SupportWinnerRank,
    `Nonsmooth.SymmetricBodyNormalization,
    `Nonsmooth.SymmetricConvexCombination,
    `Nonsmooth.SymmetricCoreDepth,
    `Nonsmooth.SymmetricHalfspaceMoment,
    `Nonsmooth.SymmetricIntervalMoment,
    `Nonsmooth.TiltedMomentCalculus,
    `Nonsmooth.TruncationMonotonicity,
    `Nonsmooth.TwoQueryOutwardCone,
    `Nonsmooth.UniformBodyLocalCertificate,
    `Nonsmooth.UnitMGFNoSpike,
    `Nonsmooth.VectorCoordinateCurvature,
    `Nonsmooth.VectorCoordinateGrowth,
    `Nonsmooth.VectorCoordinateHessianGrowth,
    `Nonsmooth.VectorCoordinateMoments,
    `Nonsmooth.VectorCoordinateSymmetry,
    `Nonsmooth.VectorGaussianEnvelope,
    `Nonsmooth.VectorPotentialContinuity,
    `Nonsmooth.VectorPotentialDifferentiation,
    `Nonsmooth.VectorPotentialExpectation,
    `Nonsmooth.VectorPotentialNormalization,
    `Nonsmooth.VectorScoreCovarianceBound,
    `Nonsmooth.VolumeContractionIteration,
    `Nonsmooth.WeightedBayes,
    `Nonsmooth.WeightedDensityLaw,
    `Nonsmooth.WeightedExpectation,
    `Nonsmooth.WeightedJointDisintegration,
    `Nonsmooth.WeightedLawTransport,
    `Nonsmooth.WeightedPosteriorKernel,
    `Nonsmooth.WeightedProductMarginal,
    `Task003Base,
    `Task003Integration,
    `Task003Integration.ProtasovBridge,
    `Task003Integration.ProtasovCoordinates,
    `Task003Integration.ProtasovPolicyTransport,
    `Task003Integration.UnconditionalMain,
    `Task003Integration.ZhangBridge,
    `Task003Integration.ZhangHardness,
    `Task003Integration.ZhangMeasure,
    `Task003Integration.ZhangMeasureCore,
    `Task003Integration.ZhangPolicy,
    `Task003Integration.ZhangScale]
  let projectModuleSet : NameSet := projectModules.foldl (fun (s : NameSet) name => s.insert name) {}
  let mut names : Array Name := #[]
  let mut theoremCount := 0
  let mut excludedUnsafe := 0
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let moduleName := (env.getModuleIdxFor? name |>.map
      (fun i => env.header.moduleNames[i.toNat]!)).getD Name.anonymous
    if projectModuleSet.contains moduleName then
      if info.isUnsafe then
        excludedUnsafe := excludedUnsafe + 1
      else
        match info with
        | .axiomInfo _ => throwError "Custom unproved project axiom: {name}"
        | .thmInfo _ => theoremCount := theoremCount + 1
        | _ => pure ()
        if info.type.hasExprMVar || info.type.hasFVar then
          throwError "Open declaration type: {name}"
        names := names.push name
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("is_theorem", toJson (match info with | .thmInfo _ => true | _ => false))])
  if names.isEmpty || theoremCount == 0 then throwError "No mathematical project declarations were loaded"
  for name in names do
    unless (env.checked.get.find? name).isSome do
      throwError "Project constant absent from kernel-checked environment: {name}"
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut closure : NameSet := {}
  let mut axiomRows : Array Json := #[]
  for name in names do
    let axioms ← Lean.collectAxioms name
    axiomRows := axiomRows.push (Json.mkObj [
      ("name", toJson name.toString), ("axioms", toJson (axioms.map Name.toString))])
    for ax in axioms do closure := closure.insert ax
    let unexpected := axioms.filter (fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound)
    unless unexpected.isEmpty do
      throwError "Unexpected transitive axiom at {name}: {unexpected}"
  let (_, bodyState) := (names.forM (AuditInfrastructure.visit env)).run {}
  unless bodyState.missing.isEmpty do
    throwError "Independent body traversal encountered missing constants: {bodyState.missing.toArray}"
  let bodyAxioms := bodyState.axioms.toArray
  unless bodyAxioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
    throwError "Independent body traversal found unexpected axioms: {bodyAxioms}"
  unless closure.toArray.all (fun a => bodyState.axioms.contains a) &&
      bodyAxioms.all (fun a => closure.contains a) do
    throwError "Upstream collector and independent body traversal disagree"
  let mut endpoints : Array Json := #[]
  let endpointNames : Array Name := #[`Nonsmooth.general_body_protasov,
    `Nonsmooth.gaussianAdaptiveHardness_proved,
    `Nonsmooth.gaussianPosteriorLogEnergyEstimate_proved,
    `Task003Integration.halfRows_map_law,
    `Task003Integration.protasovLiteratureInput_proved,
    `Task003Integration.zhangLiteratureInput_proved,
    `Task003Integration.protasovOpenPrinciple_proved,
    `Task003Integration.zhang_fixed_prior_hardness,
    `Task003.UnconditionalMain.normalized_main_unconditional,
    `Task003.UnconditionalMain.scaled_main_unconditional,
    `Task003.UnconditionalMain.paper_main_unconditional]
  for name in endpointNames do
    let some info := env.find? name | throwError "Missing endpoint: {name}"
    match info with
    | .thmInfo _ => pure ()
    | _ => throwError "Endpoint is not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "Fresh endpoint axiom check failed: {name}: {axioms}"
    let typeText ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    endpoints := endpoints.push (Json.mkObj [
      ("name", toJson name.toString),
      ("type", toJson typeText),
      ("axioms", toJson (axioms.map Name.toString))])
  let report := Json.mkObj [
    ("status", toJson "passed"),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("unsafe_compiler_artifacts_excluded", toJson excludedUnsafe),
    ("transitive_axioms", toJson (closure.toArray.map Name.toString)),
    ("independent_body_axioms", toJson (bodyAxioms.map Name.toString)),
    ("independent_body_visited", toJson bodyState.seen.size),
    ("declarations", Json.arr rows),
    ("per_declaration_axioms", Json.arr axiomRows),
    ("independent_endpoints", Json.arr endpoints)]
  liftIO (IO.println ("KERNEL_AUDIT_JSON:" ++ report.compress))
  logInfo m!"KERNEL AUDIT PASSED: {names.size} safe project declarations, {theoremCount} theorems"
