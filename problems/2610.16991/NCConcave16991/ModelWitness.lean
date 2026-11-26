import NCConcave16991.Problem

/-! # The actual problem classes are nonempty for every public parameter tuple -/

open Set

namespace NCConcave16991

noncomputable section

theorem primalObjective_zero {p : ProblemParameters} {dx dy : ℕ}
    (K : KnownDualDomain dy p.diameter) (x : PrimalSpace dx) :
    primalObjective K (fun (_ : Fin p.n) (_ : JointSpace dx dy) ↦ 0) x = 0 := by
  have he : (fun y ↦ componentAverage
      (fun (_ : Fin p.n) (_ : JointSpace dx dy) ↦ (0 : ℝ)) (jointPoint x y)) '' K.carrier = {0} := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp [componentAverage]
    · intro hv
      obtain ⟨y, hy⟩ := K.nonempty
      refine ⟨y, hy, ?_⟩
      simpa only [mem_singleton_iff, componentAverage, Finset.sum_const_zero,
        mul_zero] using hv.symm
  unfold primalObjective
  rw [he]
  simp

def zeroProblem (p : ProblemParameters) (dx dy : ℕ)
    (K : KnownDualDomain dy p.diameter) (x0 : PrimalSpace dx) : Problem p dx dy K where
  component := fun _ _ ↦ 0
  componentGradient := fun _ _ ↦ 0
  neighborhood := univ
  neighborhood_open := isOpen_univ
  domain_subset := subset_univ _
  gradient_correct := fun _ z _ ↦ hasGradientAt_const z 0
  average_dual_concave := fun x ↦ by
    simpa only [componentAverage, Finset.sum_const_zero, mul_zero] using
      concaveOn_const (0 : ℝ) K.convex
  initialPoint := x0
  value_bddBelow := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [primalObjective_zero]
  initial_gap := by
    have he : primalObjective K (fun (_ : Fin p.n) (_ : JointSpace dx dy) ↦ (0 : ℝ)) =
        fun _ ↦ 0 := funext (primalObjective_zero K)
    rw [he]
    simpa using p.gap_pos.le

theorem zeroProblem_individualSmooth (p : ProblemParameters) (dx dy : ℕ)
    (K : KnownDualDomain dy p.diameter) (x0 : PrimalSpace dx) :
    (zeroProblem p dx dy K x0).individualSmooth := by
  intro i x hx y hy
  change ‖(0 : JointSpace dx dy) - 0‖ ≤ p.L * ‖x - y‖
  simp only [sub_self, norm_zero]
  exact mul_nonneg p.L_pos.le (norm_nonneg _)

end

end NCConcave16991
