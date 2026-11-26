import SecondOrder.BernoulliSecondScore

/-!
Orthogonality of distinct score monomials under an actual independent finite
product measure. This is the L² foundation for the third-order reverse-stick
estimate; no chain-length factor enters the exact square-sum identity.
-/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι α : Type*} [Fintype ι] [Fintype α]

def scoreMonomial (X : ι → α → ℝ) (s : Finset ι) (w : ι → α) : ℝ :=
  ∏ i ∈ s, X i (w i)

theorem independent_subproduct_mean (p : ι → PMF α) (X : ι → α → ℝ)
    (s : Finset ι) :
    pmfMean (finitePiPMF p) (scoreMonomial X s) = ∏ i ∈ s, pmfMean (p i) (X i) := by
  have he (w : ι → α) : scoreMonomial X s w =
      ∏ i, if i ∈ s then X i (w i) else 1 := by simp [scoreMonomial]
  have hm (i : ι) : pmfMean (p i) (fun a => if i ∈ s then X i a else 1) =
      if i ∈ s then pmfMean (p i) (X i) else 1 := by
    split_ifs <;> simp
  calc
    _ = pmfMean (finitePiPMF p) (fun w => ∏ i, if i ∈ s then X i (w i) else 1) :=
      pmfMean_congr _ he
    _ = ∏ i, pmfMean (p i) (fun a => if i ∈ s then X i a else 1) :=
      finitePiPMF_product_mean p (fun i a => if i ∈ s then X i a else 1)
    _ = _ := by simp only [hm]; simp

theorem scoreMonomial_product_mean (p : ι → PMF α) (X : ι → α → ℝ)
    (s t : Finset ι) :
    pmfMean (finitePiPMF p) (fun w => scoreMonomial X s w * scoreMonomial X t w) =
      ∏ i, pmfMean (p i) (fun a =>
        (if i ∈ s then X i a else 1) * (if i ∈ t then X i a else 1)) := by
  have he (w : ι → α) : scoreMonomial X s w * scoreMonomial X t w =
      ∏ i, (if i ∈ s then X i (w i) else 1) * (if i ∈ t then X i (w i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [scoreMonomial]
  exact (pmfMean_congr _ he).trans (finitePiPMF_product_mean p
    (fun i a => (if i ∈ s then X i a else 1) * (if i ∈ t then X i a else 1)))

/-- Distinct subsets are orthogonal even though their monomials may share
coordinates: an index in their symmetric difference has zero mean. -/
theorem scoreMonomial_orthogonal (p : ι → PMF α) (X : ι → α → ℝ)
    (hX : ∀ i, pmfMean (p i) (X i) = 0) (s t : Finset ι) (hst : s ≠ t) :
    pmfMean (finitePiPMF p) (fun w => scoreMonomial X s w * scoreMonomial X t w) = 0 := by
  rw [scoreMonomial_product_mean]
  have hex : ∃ i, (i ∈ s ∧ i ∉ t) ∨ (i ∉ s ∧ i ∈ t) := by
    by_contra hn
    push_neg at hn
    apply hst
    ext i
    specialize hn i
    tauto
  obtain ⟨i, hi⟩ := hex
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rcases hi with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;> simpa [hs, ht] using hX i

theorem scoreMonomial_square_mean (p : ι → PMF α) (X : ι → α → ℝ)
    (s : Finset ι) :
    pmfMean (finitePiPMF p) (fun w => scoreMonomial X s w ^ 2) =
      ∏ i ∈ s, pmfMean (p i) (fun a => X i a ^ 2) := by
  have he (w : ι → α) : scoreMonomial X s w ^ 2 =
      scoreMonomial (fun i a => X i a ^ 2) s w := by
    simp only [scoreMonomial, Finset.prod_pow]
  exact (pmfMean_congr _ he).trans (independent_subproduct_mean p _ s)

/-- Exact L² identity for any finite collection of distinct score monomials,
including the degree-two and degree-three terms needed in the manuscript. -/
theorem scorePolynomial_square_mean (p : ι → PMF α) (X : ι → α → ℝ)
    (hX : ∀ i, pmfMean (p i) (X i) = 0)
    (family : Finset (Finset ι)) (c : Finset ι → ℝ) :
    pmfMean (finitePiPMF p)
        (fun w => (∑ s ∈ family, c s * scoreMonomial X s w) ^ 2) =
      ∑ s ∈ family, c s ^ 2 * ∏ i ∈ s, pmfMean (p i) (fun a => X i a ^ 2) := by
  have he (s t : Finset ι) :
      pmfMean (finitePiPMF p)
        (fun w => (c s * scoreMonomial X s w) * (c t * scoreMonomial X t w)) =
      if s = t then c s ^ 2 * ∏ i ∈ s, pmfMean (p i) (fun a => X i a ^ 2) else 0 := by
    by_cases h : s = t
    · subst t
      simp only [if_true, ← pow_two, mul_pow, pmfMean_mul,
        scoreMonomial_square_mean]
    · simp only [if_neg h, mul_mul_mul_comm, pmfMean_mul,
        scoreMonomial_orthogonal p X hX s t h, mul_zero]
  simp only [pow_two, Finset.sum_mul_sum]
  rw [pmfMean_finset_sum]
  simp only [pmfMean_finset_sum, he, Finset.sum_ite_eq, Finset.mem_univ]
  apply Finset.sum_congr rfl
  intro s hs
  simp [hs, pow_two]

/-- Specialization to the Bernoulli likelihood scores used by the paper. -/
theorem bernoulli_scorePolynomial_square_mean
    (p : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (family : Finset (Finset ι)) (c : Finset ι → ℝ) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun w => (∑ s ∈ family, c s * scoreMonomial (fun i => binaryScore (p i)) s w) ^ 2) =
      ∑ s ∈ family, c s ^ 2 * ∏ i ∈ s, (1 / (p i * (1 - p i))) := by
  have hh := scorePolynomial_square_mean
    (fun i => binaryPMF (p i) (hp0 i).le (hp1 i).le)
    (fun i => binaryScore (p i)) (fun i => binaryScore_mean (hp0 i) (hp1 i)) family c
  simpa only [bernoulliProduct, binaryScore_second_moment (hp0 _) (hp1 _)] using hh

/-- L¹ control by the exact subset energy; the size of the index set is absent.
This applies to the degree-three component after grouping ordered triples by
their underlying subsets. -/
theorem bernoulli_scorePolynomial_abs_mean_le
    (p : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (family : Finset (Finset ι)) (c : Finset ι → ℝ) :
    pmfMean (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun w => |∑ s ∈ family, c s * scoreMonomial (fun i => binaryScore (p i)) s w|) ≤
      Real.sqrt (∑ s ∈ family, c s ^ 2 * ∏ i ∈ s, (1 / (p i * (1 - p i)))) := by
  have hh := pmfMean_abs_le_sqrt
    (bernoulliProduct p (fun i => (hp0 i).le) (fun i => (hp1 i).le))
    (fun w => ∑ s ∈ family, c s * scoreMonomial (fun i => binaryScore (p i)) s w)
  simpa only [bernoulli_scorePolynomial_square_mean p hp0 hp1 family c] using hh

end
end SampleReuse
