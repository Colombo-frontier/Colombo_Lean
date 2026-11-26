import SecondOrder.CommonRandomnessEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Sample the first coordinate and then the second from its conditional law. -/
def finiteConditionalPMF (p : PMF A) (K : A → PMF B) : PMF (A × B) :=
  PMF.ofFintype (fun w => p w.1*K w.1 w.2) (by
    change (∑ w : A × B, p w.1*K w.1 w.2)=1
    rw [Fintype.sum_prod_type]
    simp_rw [←Finset.mul_sum]
    simp only [←tsum_fintype, PMF.tsum_coe, mul_one])

@[simp] theorem finiteConditionalPMF_apply (p : PMF A) (K : A → PMF B) (w : A × B) :
    finiteConditionalPMF p K w = p w.1*K w.1 w.2 := rfl

theorem finiteConditionalPMF_ne_zero (p : PMF A) (K : A → PMF B)
    (hp : ∀ a, p a≠0) (hK : ∀ a b, K a b≠0) (w : A × B) : finiteConditionalPMF p K w≠0 :=
  mul_ne_zero (hp w.1) (hK w.1 w.2)

/-- The tower formula for the actual finite joint sampling law. -/
theorem finiteConditionalPMF_mean (p : PMF A) (K : A → PMF B) (f : A × B → ℝ) :
    pmfMean (finiteConditionalPMF p K) f = pmfMean p (fun a => pmfMean (K a) (fun b => f (a,b))) := by
  simp only [pmfMean, smul_eq_mul, finiteConditionalPMF_apply, ENNReal.toReal_mul,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem finiteConditionalPMF_mean_fst (p : PMF A) (K : A → PMF B) (f : A → ℝ) :
    pmfMean (finiteConditionalPMF p K) (fun w => f w.1) = pmfMean p f := by
  rw [finiteConditionalPMF_mean]
  simp only [pmfMean_const]

theorem pmfKL_self (p : PMF A) : pmfKL p p=0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : (p a).toReal=0
  · simp [ha]
  · simp [ha]

/-- Exact conditional chain rule. The reference and true transition masses
are strictly positive, as in the manuscript's finite coefficient channels. -/
theorem pmfKL_finiteConditional (p q : PMF A) (K L : A → PMF B)
    (hp : ∀ a, p a≠0) (hq : ∀ a, q a≠0)
    (hK : ∀ a b, K a b≠0) (hL : ∀ a b, L a b≠0) :
    pmfKL (finiteConditionalPMF p K) (finiteConditionalPMF q L) =
      pmfKL p q+pmfMean p (fun a => pmfKL (K a) (L a)) := by
  have hlog (a : A) (b : B) :
      Real.log ((p a).toReal*(K a b).toReal/((q a).toReal*(L a b).toReal)) =
        Real.log ((p a).toReal/(q a).toReal)+Real.log ((K a b).toReal/(L a b).toReal) := by
    rw [mul_div_mul_comm]
    exact Real.log_mul
      (div_ne_zero (ENNReal.toReal_pos (hp a) (p.apply_ne_top a)).ne'
        (ENNReal.toReal_pos (hq a) (q.apply_ne_top a)).ne')
      (div_ne_zero (ENNReal.toReal_pos (hK a b) ((K a).apply_ne_top b)).ne'
        (ENNReal.toReal_pos (hL a b) ((L a).apply_ne_top b)).ne')
  change pmfMean (finiteConditionalPMF p K) (fun w =>
    Real.log ((finiteConditionalPMF p K w).toReal/(finiteConditionalPMF q L w).toReal)) = _
  simp only [finiteConditionalPMF_apply, ENNReal.toReal_mul, hlog]
  rw [pmfMean_add, finiteConditionalPMF_mean_fst p K (fun a => Real.log ((p a).toReal/(q a).toReal)),
    finiteConditionalPMF_mean]
  rfl

theorem pmfKL_finiteConditional_le (p q : PMF A) (K L : A → PMF B)
    (hp : ∀ a, p a≠0) (hq : ∀ a, q a≠0)
    (hK : ∀ a b, K a b≠0) (hL : ∀ a b, L a b≠0)
    (c : A → ℝ) (hc : ∀ a, pmfKL (K a) (L a)≤c a) :
    pmfKL (finiteConditionalPMF p K) (finiteConditionalPMF q L) ≤ pmfKL p q+pmfMean p c := by
  rw [pmfKL_finiteConditional p q K L hp hq hK hL]
  exact add_le_add_left (pmfMean_mono p hc) _

end
end SecondOrder
