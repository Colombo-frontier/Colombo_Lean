import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic

/-! Normalized Haar probability on the actual finite-dimensional orthogonal group. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace Bilevel.OrthogonalHaar

abbrev Group (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

instance matrixSecondCountable (d : ℕ) : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))

instance secondCountable (d : ℕ) : SecondCountableTopology (Group d) :=
  TopologicalSpace.secondCountableTopology_induced _ _
    (fun A : Group d => A.val)

theorem column_square_sum (d : ℕ) (A : Group d) (j : Fin d) :
    ∑ i, (A i j) ^ 2 = 1 := by
  have h := congrArg (fun B : Matrix (Fin d) (Fin d) ℝ => B j j) A.property.1
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
    pow_two] using h

theorem entry_bound (d : ℕ) (A : Group d) (i j : Fin d) : |A i j| ≤ 1 := by
  have h : (A i j) ^ 2 ≤ ∑ k, (A k j) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A k j)) (Finset.mem_univ i)
  rw [column_square_sum] at h
  exact (sq_le_one_iff_abs_le_one _).mp h

theorem carrier_closed (d : ℕ) : IsClosed (Matrix.orthogonalGroup (Fin d) ℝ : Set (Matrix (Fin d) (Fin d) ℝ)) := by
  have he : (Matrix.orthogonalGroup (Fin d) ℝ : Set (Matrix (Fin d) (Fin d) ℝ)) =
      {A | Aᵀ * A = 1} := by
    ext A
    change A ∈ Matrix.orthogonalGroup (Fin d) ℝ ↔ Aᵀ * A = 1
    rw [Matrix.mem_unitaryGroup_iff']
    rfl
  rw [he]
  apply isClosed_eq _ continuous_const
  fun_prop

theorem carrier_compact (d : ℕ) : IsCompact (Matrix.orthogonalGroup (Fin d) ℝ : Set (Matrix (Fin d) (Fin d) ℝ)) := by
  have hbox : IsCompact {A : Matrix (Fin d) (Fin d) ℝ | ∀ i j, A i j ∈ Set.Icc (-1) 1} :=
    by
      have h := isCompact_univ_pi (fun _ : Fin d => isCompact_univ_pi
        (fun _ : Fin d => (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1))))
      have he : {A : Matrix (Fin d) (Fin d) ℝ | ∀ i j, A i j ∈ Set.Icc (-1) 1} =
          Set.univ.pi (fun _ : Fin d => Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1)) := by
        ext A
        simp [Set.mem_pi, Pi.le_def, forall_and]
        rfl
      rw [he]
      exact h
  apply hbox.of_isClosed_subset (carrier_closed d)
  intro A hA i j
  exact abs_le.mp (entry_bound d ⟨A, hA⟩ i j)

instance compact (d : ℕ) : CompactSpace (Group d) :=
  isCompact_iff_compactSpace.mp (carrier_compact d)

instance continuousMul (d : ℕ) : ContinuousMul (Group d) := by
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

instance continuousInv (d : ℕ) : ContinuousInv (Group d) := by
  refine ⟨?_⟩
  apply Continuous.subtype_mk
  exact continuous_subtype_val.star

instance topologicalGroup (d : ℕ) : IsTopologicalGroup (Group d) := {}

instance measurableSpace (d : ℕ) : MeasurableSpace (Group d) := borel (Group d)
instance borelSpace (d : ℕ) : BorelSpace (Group d) := ⟨rfl⟩

def law (d : ℕ) : Measure (Group d) := Measure.haarMeasure ⊤

instance probability (d : ℕ) : IsProbabilityMeasure (law d) := by
  refine ⟨?_⟩
  exact Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Group d)))

instance leftInvariant (d : ℕ) : Measure.IsMulLeftInvariant (law d) :=
  Measure.isMulLeftInvariant_haarMeasure _

instance rightInvariant (d : ℕ) : Measure.IsMulRightInvariant (law d) := by
  refine ⟨fun A => ?_⟩
  have h := Measure.haarMeasure_unique ((law d).map (fun B => B * A))
    (⊤ : TopologicalSpace.PositiveCompacts (Group d))
  change (law d).map (fun B => B * A) = _ at h
  simpa only [TopologicalSpace.PositiveCompacts.coe_top, Measure.map_apply
    (measurable_mul_const A) MeasurableSet.univ, Set.preimage_univ, measure_univ,
    one_smul] using h

end Bilevel.OrthogonalHaar
