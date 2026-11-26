import SampleReuse.ReverseStickThirdCalculus

/-! Normalized third derivative of a finite product, as a genuine jet identity. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def normalizedThirdScore {ι : Type*} (s : Finset ι)
    (a b c ab ac bc abc : ι → ℝ) : ℝ :=
  (∑ i ∈ s, abc i) +
  (∑ i ∈ s, ab i) * (∑ i ∈ s, c i) +
  (∑ i ∈ s, ac i) * (∑ i ∈ s, b i) +
  (∑ i ∈ s, bc i) * (∑ i ∈ s, a i) -
  (∑ i ∈ s, (ab i * c i + ac i * b i + bc i * a i)) +
  (∑ i ∈ s, a i) * (∑ i ∈ s, b i) * (∑ i ∈ s, c i) -
  (∑ i ∈ s, a i) * (∑ i ∈ s, b i * c i) -
  (∑ i ∈ s, b i) * (∑ i ∈ s, a i * c i) -
  (∑ i ∈ s, c i) * (∑ i ∈ s, a i * b i) +
  2 * ∑ i ∈ s, a i * b i * c i

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Product normalization does not require nonzero factors; the hypotheses
are exact normalized derivative identities. For Bernoulli masses they are
obtained on the interior and then extended to boundary gates separately. -/
theorem product_normalized_third (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ContDiff ℝ 3 (f i)) (x u v w : E)
    (a b c ab ac bc abc : ι → ℝ)
    (ha : ∀ i ∈ s, fderiv ℝ (f i) x u = f i x * a i)
    (hb : ∀ i ∈ s, fderiv ℝ (f i) x v = f i x * b i)
    (hc : ∀ i ∈ s, fderiv ℝ (f i) x w = f i x * c i)
    (hab : ∀ i ∈ s, secondBilinear (f i) x u v = f i x * ab i)
    (hac : ∀ i ∈ s, secondBilinear (f i) x u w = f i x * ac i)
    (hbc : ∀ i ∈ s, secondBilinear (f i) x v w = f i x * bc i)
    (habc : ∀ i ∈ s, thirdTrilinear (f i) x u v w = f i x * abc i) :
    thirdTrilinear (fun y => ∏ i ∈ s, f i y) x u v w =
      (∏ i ∈ s, f i x) * normalizedThirdScore s a b c ab ac bc abc := by
  induction s using Finset.induction_on with
  | empty => simp [thirdTrilinear_eq_iterated, normalizedThirdScore, iteratedFDeriv_succ_const]
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, ContDiff ℝ 3 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hfs2 : ∀ j ∈ s, ContDiff ℝ 2 (f j) :=
      fun j hj => (hfs j hj).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
    have hp : ContDiff ℝ 3 (fun y => ∏ j ∈ s, f j y) := contDiff_prod hfs
    have ha' := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hb' := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hc' := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hab' := fun j hj => hab j (Finset.mem_insert_of_mem hj)
    have hac' := fun j hj => hac j (Finset.mem_insert_of_mem hj)
    have hbc' := fun j hj => hbc j (Finset.mem_insert_of_mem hj)
    have h3 := ih hfs ha' hb' hc' hab' hac' hbc'
      (fun j hj => habc j (Finset.mem_insert_of_mem hj))
    have huv := product_normalized_jets s f hfs2 x u v a b ab ha' hb' hab'
    have huw := product_normalized_jets s f hfs2 x u w a c ac ha' hc' hac'
    have hvw := product_normalized_jets s f hfs2 x v w b c bc hb' hc' hbc'
    simp only [Finset.prod_insert hi]
    rw [thirdTrilinear_mul _ _ hfi hp, h3, huv.1, huv.2.1, huw.2.1,
      huv.2.2, huw.2.2, hvw.2.2,
      ha i (Finset.mem_insert_self _ _), hb i (Finset.mem_insert_self _ _),
      hc i (Finset.mem_insert_self _ _), hab i (Finset.mem_insert_self _ _),
      hac i (Finset.mem_insert_self _ _), hbc i (Finset.mem_insert_self _ _),
      habc i (Finset.mem_insert_self _ _)]
    simp only [normalizedThirdScore, Finset.sum_insert hi]
    ring

end
end SampleReuse
