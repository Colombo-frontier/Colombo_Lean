import Nonsmooth.RecursiveGaussianCovariance
import Nonsmooth.ResponseHistoryAugmentation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] {r : ℕ}
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem policyPosterior_covariance_of_polytope_bound {s : ℝ} (hs : 0 < s)
    (Q : Measure (Fin (r + 1) → E)) [IsProbabilityMeasure Q]
    (hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q)
    (hrow : ∀ i, GaussianPolytopeRow s (Q.map (fun a => a i)))
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) (C : ℝ)
    (hcov : ∀ (ν : Measure E) [IsProbabilityMeasure ν], GaussianPolytopeRow s ν →
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤ C * ‖v‖ ^ 2) :
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ (v : E) (i : Fin (r + 1)),
      variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ) (supportPosteriorKernel Q p ω n h) ≤ C * ‖v‖ ^ 2 := by
  let u := policyResponseQuery (k := r + 1) p ω
  have hu : ∀ j, Measurable (u j) := fun j => policyResponseQuery_measurable p hp ω j
  let X := recursiveSupportResponse u n
  let Z : (Fin (r + 1) → E) → SupportHistory E (r + 1) n := fun a => supportAugmentedTranscript p a ω n
  have hX : Measurable X := recursiveSupportResponse_measurable u hu n
  have hZ : Measurable Z := (supportAugmentedTranscript_measurable p hp n).comp
    (measurable_id.prodMk measurable_const)
  exact condDistrib_property_reencoding Q X hX id measurable_id Z hZ
    (responseHistoryAugment u n) (responseHistoryAugment_measurable u hu n)
    supportResponseErase (supportResponseErase_measurable n)
    (fun a => (responseHistoryAugment_policy p ω n a).symm)
    (fun a => (recursiveSupportResponse_policy p ω n a).symm)
    (fun ν => ∀ (v : E) (i : Fin (r + 1)),
      variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ) ν ≤ C * ‖v‖ ^ 2)
    (recursiveGaussian_covariance_of_row_bound hs Q hQ hrow u hu n C hcov)

/-- The manuscript's actual all-history row covariance assertion reduces to
a static estimate for affine Gaussian ball-polytope laws at the prescribed scale. -/
theorem gaussianSupportPosterior_covariance_of_polytope_bound
    (hcov : ∀ (ν : Measure E) [IsProbabilityMeasure ν],
      GaussianPolytopeRow ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) ν →
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤ ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ))
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin (r + 1) => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ (v : E) (i : Fin (r + 1)),
      variance (fun a : Fin (r + 1) → E => ⟪v, a i⟫_ℝ) (supportPosteriorKernel Q p ω n h) ≤
        ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  let Q := Measure.pi (fun _ : Fin (r + 1) => gaussianAmbientRowLaw E)
  have hs : 0 < (Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos))
  have hQ : iIndepFun (fun i (a : Fin (r + 1) → E) => a i) Q :=
    finiteProductKernel_independent (fun _ : Fin (r + 1) => Kernel.const Unit (gaussianAmbientRowLaw E)) ()
  have hrow : ∀ i, GaussianPolytopeRow ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹)
      (Q.map (fun a => a i)) := by
    intro i
    rw [(finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq]
    exact gaussianAmbientRow_polytope
  have hfactor (v : E) : (1 / (Module.finrank ℝ E : ℝ)) * ‖v‖ ^ 2 =
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by ring
  have hb : ∀ (ν : Measure E) [IsProbabilityMeasure ν],
      GaussianPolytopeRow ((Real.sqrt (Module.finrank ℝ E : ℝ))⁻¹) ν →
      ∀ v : E, variance (fun z : E => ⟪v, z⟫_ℝ) ν ≤ (1 / (Module.finrank ℝ E : ℝ)) * ‖v‖ ^ 2 := by
    intro ν hν hclass v
    rw [hfactor]
    exact hcov ν hclass v
  simpa only [hfactor] using
    policyPosterior_covariance_of_polytope_bound hs Q hQ hrow p hp ω n _ hb

end
end Nonsmooth
