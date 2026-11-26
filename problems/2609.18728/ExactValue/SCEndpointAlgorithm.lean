import ExactValue.SCEndpoint
import ExactValue.SCQuadratic
import ExactValue.CenteredAcceleration

open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace ExactValue
noncomputable section

def endpointQuery {d : ℕ} (R : ℝ) (n : ℕ) : Euclid d :=
  if hn : n = 0 then 0 else if hi : n - 1 < d then R • EuclideanSpace.single ⟨n - 1, hi⟩ 1 else 0

theorem endpointQuery_norm {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (n : ℕ) : ‖endpointQuery (d := d) R n‖ ≤ R := by
  unfold endpointQuery
  split_ifs <;> simp [norm_smul, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_nonneg hR, hR]

def endpointDecode (d : ℕ) (μ R : ℝ) (v : ℕ → ℝ) : Euclid d :=
  batchGradient d R v 0 - (WithLp.equiv 2 (Fin d → ℝ)).symm (fun _ => μ * R / 2)

theorem endpointDecode_continuous (d : ℕ) (μ R : ℝ) : Continuous (endpointDecode d μ R) :=
  (batchGradient_continuous d R 0).sub continuous_const

def endpointAlgorithm {d : ℕ} {R : ℝ} (hR : 0 < R) (μ : ℝ) : ValueAlgorithm d R (d + 1) where
  query n _ := ⟨endpointQuery R n, endpointQuery_norm hR.le n⟩
  output hist := ⟨(ballDomain (R / 2) (by positivity)).project ((-μ⁻¹) • endpointDecode d μ R (historyValues hist)), by
    have hp := (ballDomain (d := d) (R / 2) (by positivity)).project_mem
      ((-μ⁻¹) • endpointDecode d μ R (historyValues hist))
    have hn : ‖(ballDomain (d := d) (R / 2) (by positivity)).project
        ((-μ⁻¹) • endpointDecode d μ R (historyValues hist))‖ ≤ R / 2 := by simpa [ballDomain] using hp
    linarith⟩
  query_borel _ := continuous_const.borel_measurable
  output_borel := by
    apply Continuous.borel_measurable
    apply Continuous.subtype_mk
    exact (ballDomain (d := d) (R / 2) (by positivity)).project_continuous.comp
      (continuous_const.smul ((endpointDecode_continuous d μ R).comp
        (historyValues_continuous (d := d) (n := d + 1) R)))

theorem endpointDecode_actual {d : ℕ} {μ R : ℝ} (hR : 0 < R) {f : Euclid d → ℝ} {b : Euclid d}
    (hf : ∀ x, f x = μ / 2 * ‖x‖ ^ 2 + ⟪b, x⟫_ℝ + f 0) :
    endpointDecode d μ R (historyValues (policyHistory (endpointAlgorithm (d := d) hR μ).query f (d + 1))) = b := by
  let A := endpointAlgorithm (d := d) hR μ
  let v := historyValues (policyHistory A.query f (d + 1))
  have hbase : v 0 = f 0 := by
    rw [show v 0 = policyValue A.query f 0 from historyValues_policy A.query f 0 (by omega)]
    simp [policyValue, A, endpointAlgorithm, endpointQuery]
  have hcoord (i : Fin d) : v (i.val + 1) = f (R • EuclideanSpace.single i 1) := by
    rw [show v (i.val + 1) = policyValue A.query f (i.val + 1) from
      historyValues_policy A.query f (i.val + 1) (by omega)]
    simp [policyValue, A, endpointAlgorithm, endpointQuery, i.isLt]
  ext i
  change endpointDecode d μ R v i = b i
  simp only [endpointDecode, batchGradient, PiLp.sub_apply, WithLp.equiv_symm_pi_apply,
    Nat.zero_mul, Nat.zero_add]
  change (v (i.val + 1) - v 0) / R - μ * R / 2 = b i
  rw [hbase, hcoord]
  exact isotropic_coordinate_recovery hR.ne' hf i

theorem isotropic_minimizer {d : ℕ} {μ : ℝ} (hμ : 0 < μ) {f : Euclid d → ℝ} {b : Euclid d}
    (hf : ∀ x, f x = μ / 2 * ‖x‖ ^ 2 + ⟪b, x⟫_ℝ + f 0) :
    ∀ y, f ((-μ⁻¹) • b) ≤ f y := by
  let z := (-μ⁻¹) • b
  have hb : b = -(μ • z) := by
    dsimp [z]
    simp [smul_smul, hμ.ne']
  intro y
  have heq : f y - f z = μ / 2 * ‖y - z‖ ^ 2 := by
    rw [hf y, hf z, hb]
    simp only [inner_neg_left, real_inner_smul_left, norm_sub_sq_real]
    simp only [real_inner_comm, real_inner_self_eq_norm_sq]
    ring
  have hp : 0 ≤ μ / 2 * ‖y - z‖ ^ 2 := by positivity
  change f z ≤ f y
  linarith

theorem endpointAlgorithm_exact {d : ℕ} {μ R : ℝ} (hμ : 0 < μ) (hR : 0 < R)
    {f : Euclid d → ℝ} (hf : SCObjective d μ μ R f) :
    ∃ xstar : Euclid d, (∀ y, f xstar ≤ f y) ∧ (endpointAlgorithm hR μ).result f = xstar := by
  obtain ⟨b, hb⟩ := sc_equal_parameters_quadratic hf
  obtain ⟨xstar, hx, hmin, huniq⟩ := hf.minimizer
  have hz : (-μ⁻¹) • b = xstar := huniq _ (isotropic_minimizer hμ hb)
  refine ⟨xstar, hmin, ?_⟩
  change (ballDomain (R / 2) (by positivity)).project
    ((-μ⁻¹) • endpointDecode d μ R (historyValues (policyHistory _ f (d + 1)))) = xstar
  rw [endpointDecode_actual hR hb, hz]
  apply ClosedConvexDomain.project_eq_self
  simpa [ballDomain] using hx

theorem sc_endpoint_upper {d : ℕ} {μ R ε : ℝ} (hμ : 0 < μ) (hR : 0 < R) (hε : 0 < ε) :
    scValueComplexity d R μ μ ε ≤ (d + 1 : ℕ) := by
  apply scValueComplexity_le (endpointAlgorithm hR μ)
  intro f hf
  obtain ⟨xstar, hmin, hout⟩ := endpointAlgorithm_exact hμ hR hf
  exact ⟨xstar, hmin, by rw [hout, sub_self]; exact hε.le⟩

theorem sc_endpoint_bounds {d : ℕ} (hd : 2 ≤ d) {μ R ε : ℝ}
    (hμ : 0 < μ) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ μ * R ^ 2 / 64) :
    ENNReal.ofReal ((d : ℝ) - 1) ≤ scValueComplexity d R μ μ ε ∧
      scValueComplexity d R μ μ ε ≤ (d + 1 : ℕ) :=
  ⟨sc_quadratic_lower hd hμ le_rfl hR hε hεmax, sc_endpoint_upper hμ hR hε⟩

end
end ExactValue
