import Bilevel.SphereHaar

/-! Actual Haar orthonormal frames and deterministic finite-query concentration. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.HaarFrame
open EuclideanGaussian OrthogonalAction
set_option synthInstance.maxHeartbeats 100000

def frame (d T : ℕ) (hT : T ≤ d) (A : OrthogonalHaar.Group d) (i : Fin T) : Space d :=
  A • (EuclideanSpace.basisFun (Fin d) ℝ) (Fin.castLE hT i)

theorem frame_orthonormal (d T : ℕ) (hT : T ≤ d) (A : OrthogonalHaar.Group d) :
    Orthonormal ℝ (frame d T hT A) :=
  (((EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp (Fin.castLE hT)
    (Fin.castLE_injective hT)).comp_linearIsometryEquiv (isometry d A))

theorem frame_measurable (d T : ℕ) (hT : T ≤ d) : Measurable (frame d T hT) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_id.smul measurable_const

def frameLaw (d T : ℕ) (hT : T ≤ d) : Measure (Fin T → Space d) :=
  (OrthogonalHaar.law d).map (frame d T hT)

instance frameLaw_probability (d T : ℕ) (hT : T ≤ d) : IsProbabilityMeasure (frameLaw d T hT) :=
  isProbabilityMeasure_map (frame_measurable d T hT).aemeasurable

theorem column_tail (n T : ℕ) (hT : T ≤ n + 1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (w : Space (n + 1)) (hw : ‖w‖ = 1) (i : Fin T) :
    (OrthogonalHaar.law (n + 1)).real {A | t ≤ ⟪w, frame (n + 1) T hT A i⟫ ^ 2} ≤
      2 * Real.exp (-(n : ℝ) * t / 8) :=
  SphereHaar.haar_directional_tail n t ht ht2 w _ hw
    ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).orthonormal.norm_eq_one (Fin.castLE hT i))

theorem finite_query_tail (n T M : ℕ) (hT : T ≤ n + 1) (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 2)
    (query : Fin M → Space (n + 1)) (hq : ∀ j, ‖query j‖ = 1) :
    (OrthogonalHaar.law (n + 1)).real
      {A | ∃ j : Fin M, ∃ i : Fin T, t ≤ ⟪query j, frame (n + 1) T hT A i⟫ ^ 2} ≤
      (M : ℝ) * T * (2 * Real.exp (-(n : ℝ) * t / 8)) := by
  have he : {A | ∃ j : Fin M, ∃ i : Fin T, t ≤ ⟪query j, frame (n + 1) T hT A i⟫ ^ 2} =
      ⋃ p : Fin M × Fin T, {A | t ≤ ⟪query p.1, frame (n + 1) T hT A p.2⟫ ^ 2} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _p : Fin M × Fin T, (2 * Real.exp (-(n : ℝ) * t / 8)) := by
      apply Finset.sum_le_sum
      intro p _
      exact column_tail n T hT t ht ht2 (query p.1) (hq p.1) p.2
    _ = _ := by simp [Nat.cast_mul, mul_assoc]

end Bilevel.HaarFrame
