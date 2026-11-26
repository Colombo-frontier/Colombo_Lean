import Bilevel.TransportObserverQueryMoment

/-! The invariant posterior query moment controls the ACTUAL increase in
projection energy caused by inserting a fresh unit query direction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open EuclideanGaussian ProjectionGeometry

theorem query_energy_increment {E κ : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (U : κ → E) (I : Finset κ)
    (q : E) (hqV : q ∈ Vᗮ) (hq : ‖q‖ = 1) :
    frameEnergy (V ⊔ Submodule.span ℝ {q}) U I-frameEnergy V U I =
      ∑ i ∈ I, ⟪q,U i⟫^2 := by
  have hp : project V q = 0 := congrArg Subtype.val
    ((Submodule.orthogonalProjection_eq_zero_iff).mpr hqV)
  have he : energy V q = 0 := by simp only [energy,hp,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]
  have hd : revelationDirection V q = q := by
    simp only [revelationDirection,ProjectionGeometry.residual,hp,sub_zero,hq,inv_one,one_smul]
  have hh (u : E) : energy (V ⊔ Submodule.span ℝ {q}) u-energy V u = ⟪q,u⟫^2 := by
    rw [energy,revealedProject_eq_projection_sup V q u hq (by rw [he]; norm_num)]
    rw [revealed_energy V u q hq (by rw [he]; norm_num),hd,real_inner_comm u q]
    ring
  simp only [frameEnergy,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => hh (U i))

theorem invariant_query_insertion_moment {ι : Type*} [Fintype ι]
    (d T : ℕ) (V : Submodule ℝ (Space d)) (b : OrthonormalBasis ι ℝ Vᗮ)
    (hd : 0 < Fintype.card ι) (μ : Measure (ProjectionPosterior.Frame d T))
    [IsProbabilityMeasure μ] (hμ : ProjectionPosterior.Invariant d T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (q : Space d) (hqV : q ∈ Vᗮ) (hq : ‖q‖ = 1) :
    (∫ U, frameEnergy (V ⊔ Submodule.span ℝ {q}) U Finset.univ-
      frameEnergy V U Finset.univ ∂μ) ≤ (T:ℝ)/(Fintype.card ι : ℝ) := by
  simp_rw [query_energy_increment V _ _ q hqV hq]
  exact invariant_query_total_moment d T V b hd μ hμ hnorm q hqV hq

theorem invariant_query_insertion_failure {ι : Type*} [Fintype ι]
    (d T : ℕ) (V : Submodule ℝ (Space d)) (b : OrthonormalBasis ι ℝ Vᗮ)
    (hd : 0 < Fintype.card ι) (μ : Measure (ProjectionPosterior.Frame d T))
    [IsProbabilityMeasure μ] (hμ : ProjectionPosterior.Invariant d T V μ)
    (hnorm : ∀ᵐ U ∂μ, ∀ i, ‖U i‖ ≤ 1)
    (q : Space d) (hqV : q ∈ Vᗮ) (hq : ‖q‖ = 1) (a : ℝ) (ha : 0 < a) :
    μ.real {U | a < frameEnergy (V ⊔ Submodule.span ℝ {q}) U Finset.univ-
      frameEnergy V U Finset.univ} ≤ (T:ℝ)/((Fintype.card ι : ℝ)*a) := by
  simp_rw [query_energy_increment V _ _ q hqV hq]
  have hi := integrable_finset_sum Finset.univ
    (fun i _ => invariant_query_integrable d T μ hnorm q i)
  have hm := (mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall (fun U => Finset.sum_nonneg (fun i _ => sq_nonneg ⟪q,U i⟫))) hi a).trans
    (invariant_query_total_moment d T V b hd μ hμ hnorm q hqV hq)
  have hp : μ.real {U | a ≤ ∑ i, ⟪q,U i⟫^2} ≤ ((T:ℝ)/(Fintype.card ι : ℝ))/a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hm)
  have hsub : {U : ProjectionPosterior.Frame d T | a < ∑ i, ⟪q,U i⟫^2} ⊆
      {U | a ≤ ∑ i, ⟪q,U i⟫^2} := by
    intro U hU
    change a < ∑ i, ⟪q,U i⟫^2 at hU
    change a ≤ ∑ i, ⟪q,U i⟫^2
    exact hU.le
  simpa only [div_div] using (measureReal_mono (μ := μ) hsub).trans hp

end Bilevel.TransportObserver
