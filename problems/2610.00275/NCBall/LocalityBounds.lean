import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Derivative bounds for sums with disjoint supports

These lemmas preserve a uniform bound without multiplying it by the number of
rooms. Closed support sets suffice; derivatives vanish off them by locality.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology NNReal
namespace NCBall

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedAddCommGroup E] in
theorem norm_sum_disjoint_support (s : Finset ι) (S : ι → Set E) (v : ι → F)
    (x : E) {B : ℝ} (hB : 0 ≤ B)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hzero : ∀ i ∈ s, x ∉ S i → v i = 0)
    (hbound : ∀ i ∈ s, ‖v i‖ ≤ B) : ‖∑ i ∈ s, v i‖ ≤ B := by
  classical
  by_cases hex : ∃ i ∈ s, x ∈ S i
  · obtain ⟨i, hi, hxi⟩ := hex
    have hs : ∑ j ∈ s, v j = v i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        apply hzero j hj
        intro hxj
        exact Set.disjoint_left.mp (hdisj j hj i hi hji) hxj hxi
      · simp [hi]
    rw [hs]
    exact hbound i hi
  · have hz : ∑ i ∈ s, v i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero i hi (fun hxi => hex ⟨i, hi, hxi⟩)
    simpa [hz] using hB

theorem fderiv_zero_off_closed_support (f : E → F) (S : Set E) (hS : IsClosed S)
    (hzero : ∀ x ∉ S, f x = 0) {x : E} (hx : x ∉ S) : fderiv ℝ f x = 0 := by
  have heq : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy
    exact hzero y hy
  rw [heq.fderiv_eq, fderiv_const]
  rfl

theorem fderiv_sum_disjoint_bound (s : Finset ι) (S : ι → Set E) (f : ι → E → F)
    {B : ℝ} (hB : 0 ≤ B) (hclosed : ∀ i ∈ s, IsClosed (S i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hzero : ∀ i ∈ s, ∀ x ∉ S i, f i x = 0)
    (hdiff : ∀ i ∈ s, Differentiable ℝ (f i))
    (hbound : ∀ i ∈ s, ∀ x, ‖fderiv ℝ (f i) x‖ ≤ B) (x : E) :
    ‖fderiv ℝ (fun y => ∑ i ∈ s, f i y) x‖ ≤ B := by
  rw [fderiv_sum (fun i hi => hdiff i hi x)]
  apply norm_sum_disjoint_support s S (fun i => fderiv ℝ (f i) x) x hB hdisj
  · intro i hi hx
    exact fderiv_zero_off_closed_support (f i) (S i) (hclosed i hi) (hzero i hi) hx
  · intro i hi
    exact hbound i hi x

theorem sum_disjoint_lipschitz (s : Finset ι) (S : ι → Set E) (f : ι → E → F)
    {B : ℝ≥0} (hclosed : ∀ i ∈ s, IsClosed (S i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hzero : ∀ i ∈ s, ∀ x ∉ S i, f i x = 0)
    (hdiff : ∀ i ∈ s, Differentiable ℝ (f i))
    (hbound : ∀ i ∈ s, ∀ x, ‖fderiv ℝ (f i) x‖ ≤ B) :
    LipschitzWith B (fun x => ∑ i ∈ s, f i x) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (Differentiable.sum hdiff)
  intro x
  exact fderiv_sum_disjoint_bound s S f B.coe_nonneg hclosed hdisj hzero hdiff hbound x

end NCBall
