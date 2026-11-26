import NCConcave16991.ConditionalHaarParameter
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Actual independent product Haar laws and coordinatewise probability bounds -/

open Set MeasureTheory

namespace NCConcave16991.Haar

noncomputable section

theorem product_event_bound {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (ν : Measure Ω) (μ : Measure I) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {s : Set (Ω × I)} (hs : MeasurableSet s) {b : ℝ}
    (hbound : ∀ ω, μ.real (Prod.mk ω ⁻¹' s) ≤ b) : (ν.prod μ).real s ≤ b := by
  have hint : Integrable (s.indicator (fun _ ↦ (1:ℝ))) (ν.prod μ) :=
    (integrable_const (1:ℝ)).indicator hs
  have hpoint (ω : Ω) : ∫ x, s.indicator (fun _ ↦ (1:ℝ)) (ω,x) ∂μ = μ.real (Prod.mk ω ⁻¹' s) := by
    have he : (fun x ↦ s.indicator (fun _ ↦ (1:ℝ)) (ω,x)) =
        (Prod.mk ω ⁻¹' s).indicator (fun _ ↦ (1:ℝ)) := rfl
    rw [he, integral_indicator_const (1:ℝ) (hs.preimage measurable_prodMk_left)]
    simp only [smul_eq_mul, mul_one]
  calc
    _ = ∫ z, s.indicator (fun _ ↦ (1:ℝ)) z ∂ν.prod μ := by
      rw [integral_indicator_const (1:ℝ) hs]
      simp only [smul_eq_mul, mul_one]
    _ = ∫ ω, ∫ x, s.indicator (fun _ ↦ (1:ℝ)) (ω,x) ∂μ ∂ν := integral_prod _ hint
    _ ≤ ∫ _ : Ω, b ∂ν := integral_mono_ae hint.integral_prod_left (integrable_const b)
      (Filter.Eventually.of_forall (fun ω ↦ (hpoint ω).trans_le (hbound ω)))
    _ = b := by simp

def rotationLaw (k blocks : ℕ) : Measure (Fin blocks → OrthogonalGroup k) :=
  Measure.pi (fun _ ↦ haarLaw k)

instance rotationLaw_probability (k blocks : ℕ) : IsProbabilityMeasure (rotationLaw k blocks) := by
  unfold rotationLaw
  infer_instance

def splitRotation {k M : ℕ} (j : Fin (M + 1)) :
    (Fin (M + 1) → OrthogonalGroup k) ≃ᵐ (Fin M → OrthogonalGroup k) × OrthogonalGroup k :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) ↦ OrthogonalGroup k) j).trans
    MeasurableEquiv.prodComm

theorem splitRotation_symm_apply {k M : ℕ} (j : Fin (M + 1))
    (others : Fin M → OrthogonalGroup k) (Q : OrthogonalGroup k) :
    (splitRotation j).symm (others,Q) = Fin.insertNth j Q others := rfl

theorem splitRotation_measurePreserving {k M : ℕ} (j : Fin (M + 1)) :
    MeasurePreserving (splitRotation j) (rotationLaw k (M + 1))
      ((rotationLaw k M).prod (haarLaw k)) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) ↦ haarLaw k) j
  exact (Measure.measurePreserving_swap (μ := haarLaw k) (ν := rotationLaw k M)).comp h

/-- A uniform bound for one Haar coordinate, fixing all other rotations,
integrates to the actual finite product Haar law. -/
theorem rotation_coordinate_event_bound {k M : ℕ} (j : Fin (M + 1))
    {s : Set (Fin (M + 1) → OrthogonalGroup k)} (hs : MeasurableSet s) {b : ℝ}
    (hbound : ∀ others : Fin M → OrthogonalGroup k,
      (haarLaw k).real {Q | Fin.insertNth j Q others ∈ s} ≤ b) :
    (rotationLaw k (M + 1)).real s ≤ b := by
  let e := splitRotation (k := k) j
  have hs' : MeasurableSet (e.symm ⁻¹' s) := hs.preimage e.symm.measurable
  have he := splitRotation_measurePreserving (k := k) j
  have hp : e ⁻¹' (e.symm ⁻¹' s) = s := by ext Q; simp
  have hreal : (rotationLaw k (M + 1)).real s =
      ((rotationLaw k M).prod (haarLaw k)).real (e.symm ⁻¹' s) := by
    unfold Measure.real
    rw [← he.map_eq, Measure.map_apply e.measurable hs', hp]
  rw [hreal]
  apply independent_parameter_event_bound (rotationLaw k M) hs'
  intro others
  change (haarLaw k).real {Q | (splitRotation j).symm (others,Q) ∈ s} ≤ b
  simpa only [splitRotation_symm_apply] using hbound others

/-- An arbitrary private seed law is included in the same genuine product
probability construction; no topological assumption on the seed is needed. -/
theorem seeded_rotation_coordinate_event_bound {k M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (j : Fin (M + 1))
    {s : Set (Ω × (Fin (M + 1) → OrthogonalGroup k))} (hs : MeasurableSet s) {b : ℝ}
    (hbound : ∀ ω (others : Fin M → OrthogonalGroup k),
      (haarLaw k).real {Q | (ω, Fin.insertNth j Q others) ∈ s} ≤ b) :
    (ν.prod (rotationLaw k (M + 1))).real s ≤ b := by
  apply product_event_bound ν (rotationLaw k (M + 1)) hs
  intro ω
  apply rotation_coordinate_event_bound j (hs.preimage measurable_prodMk_left)
  exact hbound ω

theorem rotated_rows_orthonormal {n k : ℕ} (e : Fin n ↪ Fin k) (Q : OrthogonalGroup k) :
    Orthonormal ℝ (fun i ↦ orthogonalLinearIsometryEquiv Q (basisVector (e i))) := by
  have h := (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin k)).comp e e.injective
  simpa only [basisVector, Function.comp_def] using
    h.comp_linearIsometryEquiv (orthogonalLinearIsometryEquiv Q)

def rotatedRows {n k M : ℕ} (e : Fin n ↪ Fin k) (Q : Fin (M + 1) → OrthogonalGroup k)
    (i : Fin n) (j : Fin (M + 1)) : EuclideanSpace ℝ (Fin k) :=
  orthogonalLinearIsometryEquiv (Q j) (basisVector (e i))

theorem rotatedRows_orthonormal {n k M : ℕ} (e : Fin n ↪ Fin k)
    (Q : Fin (M + 1) → OrthogonalGroup k) (j : Fin (M + 1)) :
    Orthonormal ℝ (fun i ↦ rotatedRows e Q i j) := rotated_rows_orthonormal e (Q j)

theorem rotatedRows_continuous {n k M : ℕ} (e : Fin n ↪ Fin k) :
    Continuous (rotatedRows (M := M) e) :=
  continuous_pi (fun i ↦ continuous_pi (fun j ↦
    (continuous_orthogonalLinearIsometryEquiv_apply (basisVector (e i))).comp (continuous_apply j)))

end

end NCConcave16991.Haar
