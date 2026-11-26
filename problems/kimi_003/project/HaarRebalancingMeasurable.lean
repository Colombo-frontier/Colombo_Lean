import HaarRebalancingRootMoment
open MeasureTheory Set
namespace Task006.HaarRebalancing

theorem measurableSet_all_column_moment_lt {d : ℕ}
    {Φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ}
    (hΦ : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => Φ p.1 p.2))
    (M : ℝ) : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × OrthogonalGroup d |
      ∀ i : Fin d, Φ p.1 (column p.2 i) < M} := by
  have heq : {p : EuclideanSpace ℝ (Fin d) × OrthogonalGroup d |
      ∀ i : Fin d, Φ p.1 (column p.2 i) < M} =
      ⋂ i : Fin d, {p | Φ p.1 (column p.2 i) < M} := by ext p; simp
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  have hcol : Measurable (fun p : EuclideanSpace ℝ (Fin d) × OrthogonalGroup d => column p.2 i) :=
    (measurable_column i).comp measurable_snd
  have hpair : Measurable (fun p : EuclideanSpace ℝ (Fin d) × OrthogonalGroup d => (p.1, column p.2 i)) :=
    measurable_fst.prodMk hcol
  exact measurableSet_lt (hΦ.comp hpair) measurable_const

end Task006.HaarRebalancing
