import GradientHessian.FirstHeightTransition

/-! Complete ordered outer-latch activation once the proven child interface
and its bounded-lower-coordinate values are substituted. The source leaf
specialization supplies these through its actual numerical localization. -/

noncomputable section
namespace GradientHessian.FirstHeight
open EuclideanRegisters InnerCoordinates

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem activation_at_bounded_lower
    (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ)
    {A₀ : ℝ} (hA : 0 ≤ A₀) (v : Fin (b + 1) → Fin (k + 2) → E) {l : ℝ} (hl : 0 ≤ l)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i))
    (ho : ∀ i, ContDiff ℝ 3 (childPort i)) (hv : ∀ i j, ‖v i j‖ = 1)
    (hchild : ∀ i d, 0 ≤ d → ∀ y, ‖gradient (fun x => child i x - d * childPort i x) y‖ ≤ 1 →
      childPort i y = 1)
    (Z : Space F E (b + 1) k)
    (hval : ∀ j, -A₀ ≤ child j (numerical F E (b + 1) (k + 2) Z) -
      Q (numerical F E (b + 1) (k + 2) Z) ∧
      child j (numerical F E (b + 1) (k + 2) Z) - Q (numerical F E (b + 1) (k + 2) Z) ≤ 0)
    (hop : ∀ j, childPort j (numerical F E (b + 1) (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1)
    (hg : ‖gradient (driven Q child childPort (A₀ + 56) v l) Z‖ ≤ 1) :
    ∀ i, Inner.ports v Z i = 1 := by
  intro i
  induction i using (measure (fun j : Fin (b + 1) => j.val)).wf.induction with
  | h i ih =>
    have hprev : ∀ j, j < i → Inner.ports v Z j = 1 := fun j hj => ih j hj
    by_cases hi : Inner.ports v Z i = 1
    · exact hi
    · have hp := Inner.ports_bounds v Z i
      by_cases hz : Inner.ports v Z i = 0
      · exact (first_zero_impossible Q child childPort (A₀ + 56) v hl hQ hc ho Z i
          (hv i) (hchild i) hprev hz hg).elim
      · exact (first_transition_impossible Q child childPort hA v hl hQ hc ho Z i
          (hv i _) hprev hval hop (lt_of_le_of_ne hp.1 (Ne.symm hz))
          (lt_of_le_of_ne hp.2 hi) hg).elim

end GradientHessian.FirstHeight
