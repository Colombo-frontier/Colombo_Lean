import StandardRationalPrefix254
import RationalUniformBudget254

noncomputable section
open Filter
open scoped Topology
namespace Paper254

theorem standardMasterError_tends_zero (T K : ℕ) :
    Tendsto (standardMasterError T K) atTop (𝓝 0) := by
  have hh := dyadic_inverse_tends_zero.const_mul (6*(standardLiveCap T K:ℝ))
  simpa only [standardMasterError,mul_zero] using hh

theorem standardBirthMass_lower (T K p : ℕ) (hp : standardMasterError T K p≤1) :
    1/(2*(K+1:ℝ))≤standardBirthMass T K p := by
  unfold standardMasterError at hp
  unfold standardBirthMass
  apply one_div_le_one_div_of_le (by positivity)
  have hx : 3*(standardLiveCap T K:ℝ)*((2:ℝ)^p)⁻¹≤1 := by nlinarith
  have hk : (0:ℝ)≤K := by positivity
  nlinarith

/-- One precision controls every standard master update and preserves a
birth mass within a constant factor of the exact scale prior. -/
theorem exists_standardMasterPrecision (T K : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃ p,standardMasterError T K p≤eps ∧
      1+3*(standardLiveCap T K:ℝ)*((2:ℝ)^p)⁻¹≤2 ∧
      1/(2*(K+1:ℝ))≤standardBirthMass T K p := by
  have hh := (standardMasterError_tends_zero T K).eventually
    (gt_mem_nhds (lt_min heps (by norm_num : (0:ℝ)<1)))
  obtain ⟨p,hp⟩ := hh.exists
  have he : standardMasterError T K p≤eps := (hp.trans_le (min_le_left _ _)).le
  have h1 : standardMasterError T K p≤1 := (hp.trans_le (min_le_right _ _)).le
  refine ⟨p,he,?_,standardBirthMass_lower T K p h1⟩
  unfold standardMasterError at h1
  nlinarith

theorem standardMaster_log_budget (T K p : ℕ) (hT : 0<T)
    (hp : standardMasterError T K p≤1) :
    Real.log ((T:ℝ)/standardBirthMass T K p)≤Real.log (2*T*(K+1:ℝ)) := by
  have hq := standardBirthMass_pos T K p
  apply Real.log_le_log (div_pos (by exact_mod_cast hT) hq)
  apply (div_le_iff₀ hq).mpr
  have hh := standardBirthMass_lower T K p hp
  have hh' : 1≤2*(K+1:ℝ)*standardBirthMass T K p :=
    by simpa [mul_comm] using (div_le_iff₀ (by positivity : 0<2*(K+1:ℝ))).mp hh
  have ht : (0:ℝ)≤T := by positivity
  nlinarith

theorem standardMaster_normalized_log_budget (T p : ℕ) (hT : 0<T)
    (hp : standardMasterError T (scaleCount T) p≤1) :
    Real.log ((T:ℝ)/standardBirthMass T (scaleCount T) p)≤2*logFactor T := by
  apply (standardMaster_log_budget T (scaleCount T) p hT hp).trans
  have ht : (1:ℝ)≤T := by exact_mod_cast hT
  have hk : (scaleCount T:ℝ)≤T := by exact_mod_cast Nat.log_le_self 2 T
  have hprod : 2*T*(scaleCount T+1:ℝ)≤(2*T)^2 := by nlinarith
  have hh := Real.log_le_log (by positivity : 0<2*T*(scaleCount T+1:ℝ)) hprod
  rw [Real.log_pow] at hh
  unfold logFactor
  norm_num at hh ⊢
  linarith

theorem explicit_standardMasterPrecision (T K s v : ℕ)
    (hN : (standardLiveCap T K:ℝ)≤(2:ℝ)^v) :
    standardMasterError T K (s+v+3)≤((2:ℝ)^s)⁻¹ ∧
      standardMasterError T K (s+v+3)≤1 := by
  have hs : (0:ℝ)<2^s := by positivity
  have hv : (0:ℝ)<2^v := by positivity
  have hp : (2:ℝ)^(s+v+3)=8*2^s*2^v := by simp only [pow_add]; ring
  have he : standardMasterError T K (s+v+3)≤((2:ℝ)^s)⁻¹ := by
    unfold standardMasterError
    rw [hp,←div_eq_mul_inv,inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity) hs).mpr
    nlinarith [mul_le_mul_of_nonneg_right hN hs.le]
  refine ⟨he,he.trans ?_⟩
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

end Paper254
#print axioms Paper254.exists_standardMasterPrecision
#print axioms Paper254.standardMaster_log_budget
#print axioms Paper254.standardMaster_normalized_log_budget
#print axioms Paper254.explicit_standardMasterPrecision
