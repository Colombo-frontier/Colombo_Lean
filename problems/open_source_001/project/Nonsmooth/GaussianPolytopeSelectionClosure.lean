import Nonsmooth.GaussianPolytopeLoserModel
import Nonsmooth.SelectionCovarianceCriterion

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianPolytopeRow_halfspace_closed {s : ℝ} (hs : 0 < s)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : GaussianPolytopeRow s ν) (q : E) (y : ℝ)
    (hp : ν {z : E | ⟪z, q⟫_ℝ ≤ y} ≠ 0) :
    GaussianPolytopeRow s (ν[|{z : E | ⟪z, q⟫_ℝ ≤ y}]) := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · have hX : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
    have he := constant_real_observation_condition (Measure.dirac x) _ hX ⟪x, q⟫_ℝ
      (ae_eq_dirac (fun z => ⟪z, q⟫_ℝ)) (Iic y) measurableSet_Iic hp
    change (Measure.dirac x)[|{z : E | ⟪z, q⟫_ℝ ≤ y}] = Measure.dirac x at he
    rw [he]
    exact Or.inl ⟨x, rfl⟩
  · exact gaussianPolytopeModel_halfspace_closed hs M q y hp

/-- Every projection is either already determined or has no atoms. -/
theorem gaussianPolytopeRow_projection_dichotomy {s : ℝ} (hs : 0 < s)
    (ν : Measure E) (hν : GaussianPolytopeRow s ν) (q : E) :
    (∃ c : ℝ, ∀ᵐ z ∂ν, ⟪z, q⟫_ℝ = c) ∨ ∀ y : ℝ, ν {z : E | ⟪z, q⟫_ℝ = y} = 0 := by
  rcases hν with ⟨x, rfl⟩ | ⟨M, rfl⟩
  · exact Or.inl ⟨⟪x, q⟫_ℝ, ae_eq_dirac (fun z => ⟪z, q⟫_ℝ)⟩
  · by_cases hv : gaussianPolytopeQueryVector M q = 0
    · refine Or.inl ⟨⟪M.origin, q⟫_ℝ, ?_⟩
      have hX : Measurable (fun z : E => ⟪z, q⟫_ℝ) := by fun_prop
      apply (ae_map_iff (gaussianPolytopeModelMap_measurable s M).aemeasurable
        (measurableSet_eq_fun hX measurable_const)).mpr
      apply Eventually.of_forall
      intro z
      simp only [gaussianPolytopeModelMap_inner, hv, inner_zero_right, mul_zero, add_zero]
    · exact Or.inr (gaussianPolytopeModel_hyperplane_zero hs M q hv)

theorem gaussianPolytopeRow_loser_closed {s : ℝ} (hs : 0 < s)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : GaussianPolytopeRow s ν)
    (q : E) {k : ℕ} (w i : Fin k) (y : ℝ)
    (hpos : ν (Prod.mk (w, y) ⁻¹' supportLoserRegion q i) ≠ 0) :
    GaussianPolytopeRow s (ν[|Prod.mk (w, y) ⁻¹' supportLoserRegion q i]) := by
  rcases gaussianPolytopeRow_projection_dichotomy hs ν hν q with ⟨c, hc⟩ | hzero
  · have hdecision : ∀ᵐ z ∂ν, (z ∈ Prod.mk (w, y) ⁻¹' supportLoserRegion q i) ↔
        (c ≤ y ∧ (¬ i < w ∨ c < y)) := by
      filter_upwards [hc] with z hz
      change (⟪z, q⟫_ℝ ≤ y ∧ (¬ i < w ∨ ⟪z, q⟫_ℝ < y)) ↔ _
      rw [hz]
    rw [cond_eq_self_of_ae_event_decision ν _
      (measurable_prodMk_left (supportLoserRegion_measurable q i)) _ hdecision hpos]
    exact hν
  · have hset := supportLoserRegion_ae_halfspace ν hzero w i y
    have he : ν[|Prod.mk (w, y) ⁻¹' supportLoserRegion q i] =
        ν[|{z : E | ⟪z, q⟫_ℝ ≤ y}] :=
      congrArg₂ (fun (c : ENNReal) (μ : Measure E) => c⁻¹ • μ)
        (measure_congr hset) (Measure.restrict_congr_set hset)
    rw [measure_congr hset] at hpos
    rw [he]
    exact gaussianPolytopeRow_halfspace_closed hs ν hν q y hpos

theorem gaussianPolytopeSelection_closed {s : ℝ} (hs : 0 < s) {n : ℕ}
    (ν : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, GaussianPolytopeRow s (ν i)) (q : E) :
    ∀ᵐ h ∂(Measure.pi ν).map (supportSingleObservation q),
      ∀ i, GaussianPolytopeRow s (supportSelectionRowKernel ν q i h) := by
  apply supportSelection_row_property ν q (fun _ μ => GaussianPolytopeRow s μ) hν
    (fun i => gaussianPolytopeRow_projection_closed hs (ν i) (hν i) q)
  intro w i y _ hp
  exact gaussianPolytopeRow_loser_closed hs (ν i) (hν i) q w i y hp

/-- The concrete row class is preserved by the actual posterior after a
maximum-and-least-index observation, including ties and determined rows. -/
theorem gaussianPolytopeSingleObservation_rows_closed {s : ℝ} (hs : 0 < s) {n : ℕ}
    (ν : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, GaussianPolytopeRow s (ν i)) (q : E) :
    ∀ᵐ h ∂(Measure.pi ν).map (supportSingleObservation q),
      ∀ i, GaussianPolytopeRow s
        ((condDistrib id (supportSingleObservation q) (Measure.pi ν) h).map (fun a => a i)) := by
  filter_upwards [gaussianPolytopeSelection_closed hs ν hν q,
    supportSelectionKernel_ae_eq_condDistrib ν q] with h hh he
  intro i
  rw [← he]
  obtain ⟨w, y⟩ := h
  rw [supportSelectionKernel_coordinate]
  exact hh i

end
end Nonsmooth
