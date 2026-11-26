import SampleReuse.ReverseStickThirdOrthogonality

/-! L² bounds for ordered score terms with bounded support multiplicity. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {I J ι α : Type*} [Fintype I] [Fintype ι] [Fintype α]

theorem sum_grouped_weight [DecidableEq J] (support : I → J) (c : I → ℝ) (W : J → ℝ) :
    (∑ s ∈ Finset.univ.image support,
      (∑ i ∈ Finset.univ.filter (fun i => support i = s), c i) * W s) =
      ∑ i, c i * W (support i) := by
  calc
    _ = ∑ s ∈ Finset.univ.image support,
        ∑ i ∈ Finset.univ.filter (fun i => support i = s), c i * W (support i) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun i (_ : i ∈ Finset.univ) => Finset.mem_image_of_mem support (Finset.mem_univ i)) _

/-- Ordered pairs/triples may repeat an unordered subset. Bounded fiber
cardinality, rather than the number of blocks, bounds the resulting L² cost. -/
theorem scoreFamily_square_mean_le
    (p : ι → PMF α) (X : ι → α → ℝ) (hX : ∀ i, pmfMean (p i) (X i) = 0)
    (support : I → Finset ι) (c : I → ℝ) (K : ℕ)
    (hK : ∀ s ∈ Finset.univ.image support,
      (Finset.univ.filter (fun i => support i = s)).card ≤ K) :
    pmfMean (finitePiPMF p) (fun w => (∑ i, c i * scoreMonomial X (support i) w) ^ 2) ≤
      (K : ℝ) * ∑ i, c i ^ 2 * ∏ j ∈ support i, pmfMean (p j) (fun a => X j a ^ 2) := by
  let family := Finset.univ.image support
  let grouped := fun s => ∑ i ∈ Finset.univ.filter (fun i => support i = s), c i
  let W := fun s : Finset ι => ∏ j ∈ s, pmfMean (p j) (fun a => X j a ^ 2)
  have hW (s : Finset ι) : 0 ≤ W s :=
    Finset.prod_nonneg (fun j _ => pmfMean_nonneg _ (fun a => sq_nonneg (X j a)))
  have he (w : ι → α) : (∑ i, c i * scoreMonomial X (support i) w) =
      ∑ s ∈ family, grouped s * scoreMonomial X s w :=
    (sum_grouped_weight support c (fun s => scoreMonomial X s w)).symm
  have hsq (s : Finset ι) (hs : s ∈ family) :
      grouped s ^ 2 ≤ (K : ℝ) * ∑ i ∈ Finset.univ.filter (fun i => support i = s), c i ^ 2 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ.filter (fun i => support i = s)) (fun _ => (1 : ℝ)) c
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hK s hs)
      (Finset.sum_nonneg (fun i _ => sq_nonneg (c i))))
  calc
    _ = ∑ s ∈ family, grouped s ^ 2 * W s := by
      have hr := scorePolynomial_square_mean p X hX family grouped
      simpa only [← he] using hr
    _ ≤ ∑ s ∈ family,
        ((K : ℝ) * ∑ i ∈ Finset.univ.filter (fun i => support i = s), c i ^ 2) * W s :=
      Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_right (hsq s hs) (hW s))
    _ = (K : ℝ) * ∑ s ∈ family,
        (∑ i ∈ Finset.univ.filter (fun i => support i = s), c i ^ 2) * W s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by dsimp only [family]; rw [sum_grouped_weight]

end
end SampleReuse
