import SecondOrder.FiniteResponseEntropy

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]

def finiteProdPMF (r : PMF A) (p : PMF B) : PMF (A × B) :=
  PMF.ofFintype (fun w => r w.1*p w.2) (by
    change (∑ w : A × B, r w.1*p w.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    have hp : ∑ b, p b = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    simp only [hp, mul_one]
    simpa only [tsum_fintype] using r.tsum_coe)

@[simp] theorem finiteProdPMF_apply (r : PMF A) (p : PMF B) (w : A × B) :
    finiteProdPMF r p w = r w.1*p w.2 := rfl

theorem finiteProdPMF_ne_zero (r : PMF A) (p : PMF B)
    (hr : ∀ a, r a ≠ 0) (hp : ∀ b, p b ≠ 0) (w : A × B) : finiteProdPMF r p w ≠ 0 :=
  mul_ne_zero (hr w.1) (hp w.2)

theorem finiteProdPMF_toMeasure [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] (r : PMF A) (p : PMF B) :
    (finiteProdPMF r p).toMeasure = r.toMeasure.prod p.toMeasure := by
  apply Measure.ext_of_singleton
  intro w
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), finiteProdPMF_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- Shared, independently sampled past coefficients have exactly zero
extra relative-entropy cost. Only the newly changed law contributes. -/
theorem pmfKL_common_left (r : PMF A) (p q : PMF B) (hr : ∀ a, r a ≠ 0) :
    pmfKL (finiteProdPMF r p) (finiteProdPMF r q) = pmfKL p q := by
  have hc (a : A) : (r a).toReal ≠ 0 := (ENNReal.toReal_pos (hr a) (r.apply_ne_top a)).ne'
  simp only [pmfKL, finiteProdPMF_apply, ENNReal.toReal_mul, Fintype.sum_prod_type,
    mul_div_mul_left _ _ (hc _), mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, pmf_toReal_sum, one_mul]

theorem klDiv_common_left [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (r : PMF A) (p q : PMF B) (hr : ∀ a, r a ≠ 0) (hq : ∀ b, q b ≠ 0) :
    klDiv (r.toMeasure.prod p.toMeasure) (r.toMeasure.prod q.toMeasure) =
      klDiv p.toMeasure q.toMeasure := by
  rw [← finiteProdPMF_toMeasure, ← finiteProdPMF_toMeasure,
    klDiv_pmf _ _ (finiteProdPMF_ne_zero r q hr hq), klDiv_pmf p q hq,
    pmfKL_common_left r p q hr]

theorem klDiv_common_response [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    {C : Type*} [MeasurableSpace C] [MeasurableSingletonClass C]
    (r : PMF A) (p q : PMF B) (hr : ∀ a, r a ≠ 0) (hp : ∀ b, p b ≠ 0)
    (hq : ∀ b, q b ≠ 0) (Φ : A × B → C) :
    klDiv ((r.toMeasure.prod p.toMeasure).map Φ) ((r.toMeasure.prod q.toMeasure).map Φ) ≤
      klDiv p.toMeasure q.toMeasure := by
  rw [← klDiv_common_left r p q hr hq, ← finiteProdPMF_toMeasure, ← finiteProdPMF_toMeasure]
  exact klDiv_finite_response _ _ (finiteProdPMF_ne_zero r p hr hp)
    (finiteProdPMF_ne_zero r q hr hq) Φ

end
end SecondOrder
