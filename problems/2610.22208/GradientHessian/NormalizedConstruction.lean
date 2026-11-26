import GradientHessian.HigherHierarchyRegularity
import GradientHessian.PresampledConstruction

/-! Actual normalized admissible objectives in the declared Euclidean
dimension, including almost-everywhere admissibility under the source law. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

def normalizedGapConstant (K : ℝ) : ℝ := normalizationScale K * gapConstant K

theorem normalizedGapConstant_pos {K : ℝ} (hK : 0 ≤ K) : 0 < normalizedGapConstant K :=
  mul_pos (normalizationScale_pos K) (gapConstant_pos hK)

variable {Y E : Type u} {H : ℕ → Type u} {m N : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)] [∀ t, CompleteSpace (H t)]

def normalizedEuclideanScalar (K : ℝ) (t : ℕ) (d : Data Y E H m t)
    (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t) : Model.Point N → ℝ :=
  fun x => normalizedScalar K t d (e x)

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem isometry_norm_le (t : ℕ) (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t) :
    ‖e.toLinearIsometry.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul]
    using (le_rfl : ‖x‖ ≤ ‖x‖)

theorem normalizedEuclideanScalar_admissible {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m t) (hd : Valid Y E H m t d)
    (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t) :
    Model.Admissible (normalizedGapConstant K * 8^(t+1) * (m+1)) (normalizedEuclideanScalar K t d e) := by
  let L := e.toLinearIsometry.toContinuousLinearMap
  have hf : ContDiff ℝ 3 (normalizedEuclideanScalar K t d e) :=
    (normalizedScalar_contDiff hK t d).comp L.contDiff
  have hD (x : Model.Point N) : ‖iteratedFDeriv ℝ 3 (normalizedEuclideanScalar K t d e) x‖ ≤ 1 :=
    (Inner.derivative_comp_linear_le L (isometry_norm_le t e) (normalizedScalar_contDiff hK t d)
      (n := 3) le_rfl x).trans (normalizedScalar_third_le_one hK t d hd (e x))
  have hb := (normalizationScale_pos K).le
  have hl (x : Model.Point N) :
      normalizationScale K * (-energy m K t-Inner.innerConstant*(m+1:ℝ)) ≤ normalizedEuclideanScalar K t d e x :=
    Normalization.rescale_lower hb (scalar_lower hK t d hd) (e x)
  apply Model.admissible_of_lower_bound (hf.of_le (by decide : (2:WithTop ℕ∞) ≤ 3)) hl
  · have he := energy_le_source_height m (K := K) (by linarith) t
    have hp : (1:ℝ) ≤ 8^(t+1) := one_le_pow₀ (by norm_num)
    have hi := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp Inner.innerConstant_pos.le) (by positivity : (0:ℝ) ≤ m+1)
    have hraw : energy m K t+Inner.innerConstant*(m+1:ℝ) ≤ gapConstant K*8^(t+1)*(m+1) := by
      unfold gapConstant
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hraw hb
    have hz : normalizedEuclideanScalar K t d e 0 = normalizationScale K*(-10*InverseGate.H₀^2) := by
      simp only [normalizedEuclideanScalar, map_zero, normalizedScalar, Normalization.rescale_zero,
        scalar_zero hK t d hd]
    rw [hz]
    unfold normalizedGapConstant
    have hn := mul_nonneg hb (sq_nonneg InverseGate.H₀)
    nlinarith
  · exact Normalization.hessian_lipschitz_of_third_bound hf 1 hD

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem normalizedEuclideanScalar_fderiv {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m t) (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t) (x : Model.Point N) :
    fderiv ℝ (normalizedEuclideanScalar K t d e) x =
      (fderiv ℝ (scalar K t d) ((normalizationScale K)⁻¹ • e x)).comp
        e.toLinearIsometry.toContinuousLinearMap := by
  have h := (((normalizedScalar_contDiff hK t d).differentiable (by norm_num) (e x)).hasFDerivAt.comp x
    e.toLinearIsometry.toContinuousLinearMap.hasFDerivAt).fderiv
  simpa only [Function.comp_def, normalizedEuclideanScalar, normalizedScalar_fderiv hK t d] using h

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem covector_norm_comp_isometry (t : ℕ) (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t)
    (l : Space Y E H m t →L[ℝ] ℝ) : ‖l.comp e.toLinearIsometry.toContinuousLinearMap‖ = ‖l‖ := by
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (isometry_norm_le t e) (norm_nonneg l)).trans_eq (mul_one _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.norm_map] using (l.comp e.toLinearIsometry.toContinuousLinearMap).le_opNorm x

theorem normalizedEuclideanScalar_stationary {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m t) (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t) (x : Model.Point N) :
    x ∈ Model.stationary (normalizedEuclideanScalar K t d e) ↔
      ‖gradient (scalar K t d) ((normalizationScale K)⁻¹ • e x)‖ ≤ 1 := by
  simp only [Model.stationary, Set.mem_setOf_eq, normalizedEuclideanScalar_fderiv hK t d e x,
    covector_norm_comp_isometry, gradient, LinearIsometryEquiv.norm_map]

omit [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)] in
theorem normalizedEuclideanScalar_ordinaryJet {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m t) (e : Model.Point N ≃ₗᵢ[ℝ] Space Y E H m t) (x : Model.Point N) :
    JetLocality.ordinaryJet (normalizedEuclideanScalar K t d e) x =
      (normalizationScale K*scalar K t d ((normalizationScale K)⁻¹ • e x),
        (fderiv ℝ (scalar K t d) ((normalizationScale K)⁻¹ • e x)).comp
          e.toLinearIsometry.toContinuousLinearMap) := by
  simp only [JetLocality.ordinaryJet, normalizedEuclideanScalar_fderiv hK t d e x]
  rfl

end GradientHessian.HigherHierarchy

namespace GradientHessian.PresampledConstruction

def normalizedObjective (Cp K : ℝ) (s : Settings) (t : ℕ) (x : Sample Cp s t) :
    Model.Point (PhysicalDimension.count Cp s.D s.M (t+1)) → ℝ :=
  HigherHierarchy.normalizedEuclideanScalar K t (coefficients Cp s t x)
    (HigherHierarchy.allocatedEuclideanEquiv Cp s.D (4096*s.J^2) t).symm

theorem normalizedObjective_admissible {K : ℝ} (hK : 16 ≤ K) (Cp : ℝ) (s : Settings) (t : ℕ) :
    ∀ᵐ x ∂law Cp s t, Model.Admissible
      (HigherHierarchy.normalizedGapConstant K * 8^(t+1) * s.M) (normalizedObjective Cp K s t x) := by
  filter_upwards [coefficients_valid Cp s t] with x hx
  simpa only [normalizedObjective, Settings.M, Nat.cast_add, Nat.cast_one] using
    HigherHierarchy.normalizedEuclideanScalar_admissible hK t (coefficients Cp s t x) hx
      (HigherHierarchy.allocatedEuclideanEquiv Cp s.D (4096*s.J^2) t).symm

end GradientHessian.PresampledConstruction
