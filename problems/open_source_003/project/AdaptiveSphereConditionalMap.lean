import AdaptiveSphereConditional

/-! Conditional symmetry tools requiring actual measure preservation only.
No measurable inverse or conditional posterior moment is assumed. -/

open MeasureTheory ProbabilityTheory Set

namespace Task006.AdaptiveSphere
noncomputable section

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

section VectorStatistics
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Observable-invariant change of variables under an arbitrary measure-preserving map. -/
theorem setIntegral_transport_of_invariant_map
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (s : Set Ω) (hs : MeasurableSet s) (hinv : T ⁻¹' s = s)
    (f g : Ω → V) (hf : Integrable f μ) (hcomp : ∀ ω, f (T ω) = g ω) :
    ∫ ω in s, g ω ∂μ = ∫ ω in s, f ω ∂μ := by
  have hind : (fun ω => (s.indicator f) (T ω)) = s.indicator g := by
    funext ω
    have hmem : T ω ∈ s ↔ ω ∈ s := by
      change ω ∈ T ⁻¹' s ↔ ω ∈ s
      rw [hinv]
    by_cases hω : ω ∈ s
    · have hTω : T ω ∈ s := hmem.mpr hω
      simp only [indicator_of_mem hTω, indicator_of_mem hω, hcomp]
    · have hTω : T ω ∉ s := fun h => hω (hmem.mp h)
      simp only [indicator_of_notMem hTω, indicator_of_notMem hω]
  have hfmap : AEStronglyMeasurable (s.indicator f) (Measure.map T μ) := by
    rw [hT.map_eq]
    exact (hf.indicator hs).aestronglyMeasurable
  have hchange := integral_map hT.measurable.aemeasurable hfmap
  rw [hT.map_eq, hind, integral_indicator hs, integral_indicator hs] at hchange
  exact hchange.symm

theorem condExp_transport_of_invariant_map
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (T : Ω → Ω) (hT : @MeasurePreserving Ω Ω mΩ mΩ T μ μ)
    (hinv : ∀ s : Set Ω, MeasurableSet[m] s → T ⁻¹' s = s)
    (f g : Ω → V) (hf : Integrable f μ) (hg : Integrable g μ)
    (hcomp : ∀ ω, f (T ω) = g ω) :
    μ[f | m] =ᵐ[μ] μ[g | m] := by
  letI : MeasurableSpace Ω := mΩ
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s hs hfinite
    exact integrable_condExp.integrableOn
  · intro s hs hfinite
    rw [setIntegral_condExp hm hg hs]
    exact setIntegral_transport_of_invariant_map T hT s (hm s hs) (hinv s hs) f g hf hcomp
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

/-- Vector-valued conditional centering, derived from oddness and the map law. -/
theorem condExp_zero_of_invariant_odd_map
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (T : Ω → Ω) (hT : @MeasurePreserving Ω Ω mΩ mΩ T μ μ)
    (hinv : ∀ s : Set Ω, MeasurableSet[m] s → T ⁻¹' s = s)
    (f : Ω → V) (hf : Integrable f μ) (hodd : ∀ ω, f (T ω) = -f ω) :
    μ[f | m] =ᵐ[μ] (fun _ => (0 : V)) := by
  letI : MeasurableSpace Ω := mΩ
  have htransport := condExp_transport_of_invariant_map m hm T hT hinv f (-f) hf hf.neg hodd
  have hneg := condExp_neg (μ := μ) f m
  filter_upwards [htransport, hneg] with ω hω hnω
  have heq : (μ[f | m]) ω = -(μ[f | m]) ω := hω.trans hnω
  have hsum : (μ[f | m]) ω + (μ[f | m]) ω = 0 := eq_neg_iff_add_eq_zero.mp heq
  have htwo : (2 : ℝ) • (μ[f | m]) ω = 0 := by simpa only [two_smul] using hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end VectorStatistics

/-- Map-law version of conditional isotropy: no inverse of the adaptive
history-dependent transformations is required. -/
theorem conditional_isotropic_second_moment_of_maps
    (d : ℕ) (hd : 0 < d) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : Fin d → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ i, Integrable (fun ω => (X i ω) ^ 2) μ)
    (hY : Integrable Y μ) (hYm : StronglyMeasurable[m] Y)
    (hsum : (fun ω => ∑ i : Fin d, (X i ω) ^ 2) =ᵐ[μ] Y)
    (hsym : ∀ i j : Fin d, ∃ T : Ω → Ω,
      @MeasurePreserving Ω Ω mΩ mΩ T μ μ ∧
      (∀ s : Set Ω, MeasurableSet[m] s → T ⁻¹' s = s) ∧
      (∀ ω, (X i (T ω)) ^ 2 = (X j ω) ^ 2))
    (i : Fin d) :
    μ[(fun ω => (X i ω) ^ 2) | m] =ᵐ[μ] (fun ω => Y ω / d) := by
  letI : MeasurableSpace Ω := mΩ
  classical
  have hpair (j : Fin d) :
      μ[(fun ω => (X j ω) ^ 2) | m] =ᵐ[μ]
        μ[(fun ω => (X i ω) ^ 2) | m] := by
    obtain ⟨T, hT, hinv, hcomp⟩ := hsym j i
    exact condExp_transport_of_invariant_map m hm T hT hinv _ _ (hX j) (hX i) hcomp
  have hall : ∀ᵐ ω ∂μ, ∀ j : Fin d,
      (μ[(fun ω => (X j ω) ^ 2) | m]) ω =
        (μ[(fun ω => (X i ω) ^ 2) | m]) ω := by
    rw [ae_all_iff]
    exact hpair
  have hcesum := condExp_finsetSum
    (s := Finset.univ) (f := fun j : Fin d => fun ω => (X j ω) ^ 2)
    (fun j _ => hX j) m
  have hsumfun : (∑ j : Fin d, fun ω => (X j ω) ^ 2) =
      (fun ω => ∑ j : Fin d, (X j ω) ^ 2) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsumfun] at hcesum
  have hceY : μ[(fun ω => ∑ j : Fin d, (X j ω) ^ 2) | m] =ᵐ[μ] Y := by
    exact (condExp_congr_ae hsum).trans
      (Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hYm hY))
  filter_upwards [hall, hcesum, hceY] with ω heq hs hy
  have hsumω : (∑ j : Fin d, (μ[(fun ω => (X j ω) ^ 2) | m]) ω) = Y ω := by
    simpa only [Finset.sum_apply] using hs.symm.trans hy
  have hconst : (∑ j : Fin d, (μ[(fun ω => (X j ω) ^ 2) | m]) ω) =
      (d : ℝ) * (μ[(fun ω => (X i ω) ^ 2) | m]) ω := by
    calc
      _ = ∑ _j : Fin d, (μ[(fun ω => (X i ω) ^ 2) | m]) ω := by
        apply Finset.sum_congr rfl
        intro j hj
        exact heq j
      _ = _ := by simp
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hd0).2
  nlinarith

#print axioms condExp_transport_of_invariant_map
#print axioms condExp_zero_of_invariant_odd_map
#print axioms conditional_isotropic_second_moment_of_maps

end
end Task006.AdaptiveSphere
