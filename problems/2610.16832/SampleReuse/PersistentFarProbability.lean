import SampleReuse.PersistentSourceLaw

/-! Far activation probability, including the final unqueried output point,
under the actual persistent full-sample table law. -/

open SecondOrder
open scoped Classical BigOperators
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type} [Fintype Handle]

theorem persistent_far_union_bound (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (N : ℕ) :
    pmfEventProbability (persistentSourceLaw d T Handle R hR)
      (fun w => decide (∃ n : Fin (N + 1), ∃ j : Fin (T + 1),
        persistentFarCoordinate P A β j n.val w)) ≤
      (N + 1 : ℕ) * (T + 1 : ℕ) * (2 * Real.exp (-(d : ℝ) / 128)) := by
  have hu := pmfEventProbability_union (persistentSourceLaw d T Handle R hR)
    (fun i : Fin (N + 1) × Fin (T + 1) => fun w => decide (persistentFarCoordinate P A β i.2 i.1.val w))
  have he : (fun w : Fin (T + 1) → PersistentBlock d Handle R =>
      decide (∃ n : Fin (N + 1), ∃ j : Fin (T + 1), persistentFarCoordinate P A β j n.val w)) =
      (fun w => decide (∃ i : Fin (N + 1) × Fin (T + 1),
        decide (persistentFarCoordinate P A β i.2 i.1.val w) = true)) := by
    funext w
    simp only [decide_eq_true_eq, Prod.exists]
  rw [he]
  apply hu.trans
  calc
    _ ≤ ∑ _i : Fin (N + 1) × Fin (T + 1), 2 * Real.exp (-(d : ℝ) / 128) :=
      Finset.sum_le_sum (fun i _ => persistent_far_coordinate_bound P A β R hR i.2 i.1.val)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]

end
end SampleReuse
