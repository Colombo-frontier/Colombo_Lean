import GradientHessian.LinearPolicyTransport

/-! Exact policy transport from a normalized Euclidean objective to its
physical scalar through the actual scale and linear isometry. All execution
identities hold for every seed and every internal-time prefix. -/

noncomputable section
namespace GradientHessian.NormalizationPolicy
open Model Machine MeasureTheory Set

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {d : ℕ}

local instance physicalFirstMeasurable : MeasurableSpace (G →L[ℝ] ℝ) := borel _
local instance physicalFirstBorel : BorelSpace (G →L[ℝ] ℝ) := ⟨rfl⟩
local instance physicalSecondMeasurable : MeasurableSpace (G →L[ℝ] G →L[ℝ] ℝ) := borel _
local instance physicalSecondBorel : BorelSpace (G →L[ℝ] G →L[ℝ] ℝ) := ⟨rfl⟩

def queryMap (b : ℝ) (e : Point d ≃ₗᵢ[ℝ] G) : Point d →L[ℝ] G :=
  b⁻¹ • e.toLinearIsometry.toContinuousLinearMap

@[simp] theorem queryMap_apply (b : ℝ) (e : Point d ≃ₗᵢ[ℝ] G) (x : Point d) :
    queryMap b e x = b⁻¹ • e x := rfl

def objective (b : ℝ) (e : Point d ≃ₗᵢ[ℝ] G) (f : G → ℝ) : Point d → ℝ :=
  JetPullback.scalar b (queryMap b e) f

theorem objective_apply (b : ℝ) (e : Point d ≃ₗᵢ[ℝ] G) (f : G → ℝ) (x : Point d) :
    objective b e f x = b*f (b⁻¹ • e x) := rfl

theorem isometry_norm_le (e : Point d ≃ₗᵢ[ℝ] G) : ‖e.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul]
    using (le_rfl : ‖x‖ ≤ ‖x‖)

theorem covector_norm (e : Point d ≃ₗᵢ[ℝ] G) (l : G →L[ℝ] ℝ) :
    ‖JetPullback.first e.toLinearIsometry.toContinuousLinearMap l‖ = ‖l‖ := by
  apply le_antisymm (JetPullback.first_norm_le _ (isometry_norm_le e) l)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  simpa only [JetPullback.first_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.norm_map]
    using (l.comp e.toLinearIsometry.toContinuousLinearMap).le_opNorm x

theorem derivative_scale_cancel {b : ℝ} (hb : b ≠ 0) (e : Point d ≃ₗᵢ[ℝ] G) (l : G →L[ℝ] ℝ) :
    b • JetPullback.first (queryMap b e) l = JetPullback.first e.toLinearIsometry.toContinuousLinearMap l := by
  ext x
  simp only [ContinuousLinearMap.smul_apply, JetPullback.first_apply, ContinuousLinearMap.comp_apply,
    queryMap_apply, map_smul, smul_eq_mul]
  field_simp

theorem objective_stationary {b : ℝ} (hb : b ≠ 0) (e : Point d ≃ₗᵢ[ℝ] G)
    {f : G → ℝ} (hf : Differentiable ℝ f) :
    stationary (objective b e f) = queryMap b e ⁻¹' {x | ‖fderiv ℝ f x‖ ≤ 1} := by
  ext x
  simp only [stationary, Set.mem_setOf_eq, Set.mem_preimage, objective,
    JetPullback.scalar_fderiv b (queryMap b e) hf, derivative_scale_cancel hb e, covector_norm]

variable [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
variable {Seed State : Type*} [MeasurableSpace Seed] [MeasurableSpace State]

def transport (P : Policy Seed State (Point d) (OrdinaryReply d) (RichReply d))
    (b : ℝ) (e : Point d ≃ₗᵢ[ℝ] G) :
    Policy Seed State G (ℝ × (G →L[ℝ] ℝ)) (ℝ × (G →L[ℝ] ℝ) × (G →L[ℝ] G →L[ℝ] ℝ)) :=
  P.transport (queryMap b e) (fun z => JetPullback.ordinary b (queryMap b e) z.2)
    (fun z => JetPullback.rich b (queryMap b e) z.2)
    (queryMap b e).continuous.measurable
    ((JetPullback.ordinary_continuous b (queryMap b e)).measurable.comp measurable_snd)
    ((JetPullback.rich_continuous b (queryMap b e)).measurable.comp measurable_snd)

variable (P : Policy Seed State (Point d) (OrdinaryReply d) (RichReply d))
    (b : ℝ) (e : Point d ≃ₗᵢ[ℝ] G) {f : G → ℝ} (hf : ContDiff ℝ 2 f)

include hf

theorem run (n : ℕ) (seed : Seed) :
    (transport P b e).run (JetLocality.ordinaryJet f) (JetLocality.richJet f) n seed =
      P.run (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) n seed :=
  P.transport_run (queryMap b e) _ _ _ _ _ _ _ _ _
    (fun x => (JetPullback.ordinary_exact b (queryMap b e) (hf.differentiable (by norm_num)) x).symm)
    (fun x => (JetPullback.rich_exact b (queryMap b e) hf x).symm) n seed

theorem output (n : ℕ) (seed : Seed) :
    (transport P b e).output ((transport P b e).run (JetLocality.ordinaryJet f) (JetLocality.richJet f) n seed) =
      (queryMap b e) (P.output (P.run (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) n seed)) := by
  rw [run P b e hf n seed]
  rfl

theorem ordinaryCount (n : ℕ) (seed : Seed) :
    (transport P b e).ordinaryCount (JetLocality.ordinaryJet f) (JetLocality.richJet f) n seed =
      P.ordinaryCount (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) n seed := by
  simp only [Policy.ordinaryCount, run P b e hf]
  rfl

theorem richCount (n : ℕ) (seed : Seed) :
    (transport P b e).richCount (JetLocality.ordinaryJet f) (JetLocality.richJet f) n seed =
      P.richCount (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) n seed := by
  simp only [Policy.richCount, run P b e hf]
  rfl

theorem hasCaps (C H : ℕ) :
    (transport P b e).HasCaps (JetLocality.ordinaryJet f) (JetLocality.richJet f) C H ↔
      P.HasCaps (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) C H := by
  simp only [Policy.HasCaps, ordinaryCount P b e hf, richCount P b e hf]

theorem terminates :
    (transport P b e).Terminates (JetLocality.ordinaryJet f) (JetLocality.richJet f) ↔
      P.Terminates (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) := by
  simp only [Policy.Terminates, run P b e hf]
  rfl

theorem terminatesAlmostSurely (μ : Measure Seed) :
    (transport P b e).TerminatesAlmostSurely (JetLocality.ordinaryJet f) (JetLocality.richJet f) μ ↔
      P.TerminatesAlmostSurely (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) μ := by
  simp only [Policy.TerminatesAlmostSurely, run P b e hf]
  rfl

theorem success (hb : b ≠ 0) :
    (transport P b e).success (JetLocality.ordinaryJet f) (JetLocality.richJet f) {x | ‖fderiv ℝ f x‖ ≤ 1} =
      P.success (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) (stationary (objective b e f)) := by
  rw [objective_stationary hb e (hf.differentiable (by norm_num))]
  ext seed
  simp only [Policy.success, Set.mem_setOf_eq, run P b e hf]
  rfl

theorem successBy (hb : b ≠ 0) (n : ℕ) :
    (transport P b e).successBy (JetLocality.ordinaryJet f) (JetLocality.richJet f) {x | ‖fderiv ℝ f x‖ ≤ 1} n =
      P.successBy (ordinaryOracle (objective b e f)) (richOracle (objective b e f)) (stationary (objective b e f)) n := by
  rw [objective_stationary hb e (hf.differentiable (by norm_num))]
  ext seed
  simp only [Policy.successBy, Set.mem_setOf_eq, run P b e hf]
  rfl

end GradientHessian.NormalizationPolicy
