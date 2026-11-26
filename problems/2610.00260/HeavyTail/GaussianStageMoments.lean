import HeavyTail.GaussianOnlineFactorMoments
import HeavyTail.AcceptedOracleRegularity

/-! Concrete accepted-law exponential moments for the Gaussian learner.
All moment, mean, centering and probability inputs are discharged from the
original private oracle contract and the public feasible-query reduction. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace HeavyTail

def acceptedBiasScale (θ : OracleParameters) (τ : ℝ) : ℝ :=
  rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1)

def acceptedMeanScale (θ : OracleParameters) (τ : ℝ) : ℝ :=
  4 * θ.G + acceptedBiasScale θ τ

def acceptedTraceScale (θ : OracleParameters) (τ : ℝ) : ℝ :=
  rejectionConstant θ.p * θ.L ^ θ.p * τ ^ (2 - θ.p)

def acceptedWeakScale (θ : OracleParameters) : ℝ :=
  (rejectionConstant θ.p) ^ θ.p⁻¹ * θ.s

def acceptedOnlineExponent (θ : OracleParameters) (τ R a η : ℝ) : ℝ :=
  GaussianEstimates.mixedConstant θ.p *
    (η ^ θ.p * (acceptedWeakScale θ * R) ^ θ.p +
      η ^ 2 * a ^ 2 * (acceptedTraceScale θ τ + (acceptedMeanScale θ τ) ^ 2))

theorem acceptedBiasScale_nonneg (θ : OracleParameters) {τ : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) : 0 ≤ acceptedBiasScale θ τ := by
  have hL := θ.s_pos.trans_le θ.s_le_L
  have ht : 0 < τ := by linarith [θ.G_pos]
  unfold acceptedBiasScale
  exact mul_nonneg (mul_nonneg (rejectionConstant_pos θ.p).le θ.s_pos.le)
    (Real.rpow_nonneg (div_nonneg hL.le ht.le) _)

theorem acceptedMeanScale_pos (θ : OracleParameters) {τ : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) : 0 < acceptedMeanScale θ τ := by
  unfold acceptedMeanScale
  linarith [θ.G_pos, acceptedBiasScale_nonneg θ hτ]

theorem acceptedTraceScale_pos (θ : OracleParameters) {τ : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) : 0 < acceptedTraceScale θ τ := by
  have hL := θ.s_pos.trans_le θ.s_le_L
  have ht : 0 < τ := by linarith [θ.G_pos]
  exact mul_pos (mul_pos (rejectionConstant_pos θ.p) (Real.rpow_pos_of_pos hL _))
    (Real.rpow_pos_of_pos ht _)

theorem acceptedWeakScale_pos (θ : OracleParameters) : 0 < acceptedWeakScale θ :=
  mul_pos (Real.rpow_pos_of_pos (rejectionConstant_pos θ.p) _) θ.s_pos

theorem acceptedWeakScale_rpow (θ : OracleParameters) :
    (acceptedWeakScale θ) ^ θ.p = rejectionConstant θ.p * θ.s ^ θ.p := by
  have hp : θ.p ≠ 0 := (lt_trans zero_lt_one θ.p_gt_one).ne'
  unfold acceptedWeakScale
  rw [Real.mul_rpow (Real.rpow_pos_of_pos (rejectionConstant_pos θ.p) _).le θ.s_pos.le,
    Real.rpow_inv_rpow (rejectionConstant_pos θ.p).le hp]

theorem acceptedOnlineExponent_nonneg (θ : OracleParameters) {τ R a η : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR : 0 ≤ R) (hη : 0 ≤ η) :
    0 ≤ acceptedOnlineExponent θ τ R a η := by
  have hfirst := mul_nonneg (Real.rpow_nonneg hη θ.p)
    (Real.rpow_nonneg (mul_nonneg (acceptedWeakScale_pos θ).le hR) θ.p)
  have hsecond := mul_nonneg (mul_nonneg (sq_nonneg η) (sq_nonneg a))
    (add_nonneg (acceptedTraceScale_pos θ hτ).le (sq_nonneg (acceptedMeanScale θ τ)))
  exact mul_nonneg (GaussianEstimates.mixedConstant_pos θ.p).le (add_nonneg hfirst hsecond)

namespace PrivateInstance
open GaussianEntropy GaussianEstimates

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem acceptedMixtureMean_distance (I : PrivateInstance B) {c : E} {R : ℝ}
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (w : SimplexPoint ι) :
    ‖finiteMixtureMean centers w.val - I.minimizer‖ ≤ 2 * R := by
  have hb := finiteMixtureMean_ball E c R centers hc w.property
  have ht := norm_sub_le_norm_sub_add_norm_sub (finiteMixtureMean centers w.val) c I.minimizer
  linarith only [hb, ht, hcenter]

def acceptedGaussianW (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (w : SimplexPoint ι) (g : E) : ℝ :=
  let z := finiteMixtureMean centers w.val
  onlineMixtureW E c a η centers w.val (B.correctedReply hR hn z g)
    (I.acceptedMean hR hn τ z) z

def acceptedGaussianComparatorFactor (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (q w : SimplexPoint ι) (g : E) : ℝ :=
  let z := finiteMixtureMean centers w.val
  Real.exp (∫ u, onlineMixtureError E η (B.correctedReply hR hn z g)
    (I.acceptedMean hR hn τ z) z u ∂physicalGaussianMixtureLaw E c a centers q.val)

/-- Actual learner factor, without separately assumed centered-noise inputs. -/
theorem acceptedGaussianW_moment (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (w : SimplexPoint ι) :
    Integrable (I.acceptedGaussianW hR hn τ c a η centers w)
      (I.acceptedRawLaw hR hn τ (finiteMixtureMean centers w.val)) ∧
    (∫ g, I.acceptedGaussianW hR hn τ c a η centers w g
      ∂I.acceptedRawLaw hR hn τ (finiteMixtureMean centers w.val)) ≤
      Real.exp (acceptedOnlineExponent θ τ R a η) := by
  let z := finiteMixtureMean centers w.val
  let b := I.acceptedMean hR hn τ z
  let ξ : E → E := fun g => B.correctedReply hR hn z g - b
  have hz : ‖z - I.minimizer‖ ≤ 2 * R := I.acceptedMixtureMean_distance centers hc hcenter w
  letI := I.acceptedRawLaw_probability hR hn hτ z hz
  have hξ : Measurable ξ := (B.correctedReply_measurable_right hR hn z).sub_const b
  have hraw := I.acceptedRawLaw_bounds hR hn hτ z hz
  have hweak : ∀ v : E, ‖v‖ = 1 →
      (∫ g, |⟪v, ξ g⟫_ℝ| ^ θ.p ∂I.acceptedRawLaw hR hn τ z) ≤ (acceptedWeakScale θ) ^ θ.p := by
    rw [acceptedWeakScale_rpow]
    exact hraw.2.2.2.2
  have h := onlineMixtureW_moment E (P := I.acceptedRawLaw hR hn τ z) (ξ := ξ) hξ
    (I.acceptedNoise_square_integrable hR hn hτ z hz) (I.acceptedNoise_centered hR hn hτ z hz)
    θ.p_gt_one θ.p_le_two (acceptedWeakScale_pos θ) hraw.2.2.2.1 hweak c b z
    (I.acceptedMean_bound hR hn hτ z hz) hη ha haR htune centers
    (center_finiteMixtureMean_distance E c R centers hc w.property) w.property
  have hobs : ∀ g, b + ξ g = B.correctedReply hR hn z g := by intro g; dsimp [ξ]; abel
  simp_rw [hobs] at h
  exact h

/-- Actual comparator factor, with Gaussian Jensen and all accepted moments derived. -/
theorem acceptedGaussianComparatorFactor_moment (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (q w : SimplexPoint ι) :
    Integrable (I.acceptedGaussianComparatorFactor hR hn τ c a η centers q w)
      (I.acceptedRawLaw hR hn τ (finiteMixtureMean centers w.val)) ∧
    (∫ g, I.acceptedGaussianComparatorFactor hR hn τ c a η centers q w g
      ∂I.acceptedRawLaw hR hn τ (finiteMixtureMean centers w.val)) ≤
      Real.exp (acceptedOnlineExponent θ τ R a η) := by
  let z := finiteMixtureMean centers w.val
  let b := I.acceptedMean hR hn τ z
  let ξ : E → E := fun g => B.correctedReply hR hn z g - b
  have hz : ‖z - I.minimizer‖ ≤ 2 * R := I.acceptedMixtureMean_distance centers hc hcenter w
  letI := I.acceptedRawLaw_probability hR hn hτ z hz
  have hξ : Measurable ξ := (B.correctedReply_measurable_right hR hn z).sub_const b
  have hraw := I.acceptedRawLaw_bounds hR hn hτ z hz
  have hweak : ∀ v : E, ‖v‖ = 1 →
      (∫ g, |⟪v, ξ g⟫_ℝ| ^ θ.p ∂I.acceptedRawLaw hR hn τ z) ≤ (acceptedWeakScale θ) ^ θ.p := by
    rw [acceptedWeakScale_rpow]
    exact hraw.2.2.2.2
  have h := comparator_exp_error_moment E (P := I.acceptedRawLaw hR hn τ z) (ξ := ξ) hξ
    (I.acceptedNoise_square_integrable hR hn hτ z hz) (I.acceptedNoise_centered hR hn hτ z hz)
    θ.p_gt_one θ.p_le_two (acceptedWeakScale_pos θ) hraw.2.2.2.1 hweak c b z
    (I.acceptedMean_bound hR hn hτ z hz) hη ha haR htune centers
    (center_finiteMixtureMean_distance E c R centers hc w.property) q.property
  have hobs : ∀ g, b + ξ g = B.correctedReply hR hn z g := by intro g; dsimp [ξ]; abel
  simp_rw [hobs] at h
  exact h

end PrivateInstance
end HeavyTail
