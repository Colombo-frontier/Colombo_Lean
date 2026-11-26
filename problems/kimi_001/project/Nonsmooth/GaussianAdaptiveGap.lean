import Nonsmooth.LinearPolicyTail
import Nonsmooth.GaussianRowGeometry
import Nonsmooth.ProductProbability

open MeasureTheory ProbabilityTheory Function Filter
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

def linearPolicyGap (p : Policy Ω S (Feasible E 1)) (ω : Ω) (T : ℕ) (a : E) : ℝ :=
  ⟪a, linearPolicyOutput p 1 ω T a⟫_ℝ + ‖a‖

theorem linearPolicyGap_measurable (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (ω : Ω) (T : ℕ) : Measurable (linearPolicyGap p ω T) := by
  have hW : Measurable (linearPolicyOutput p 1 ω T) :=
    (linearPolicyOutput_joint_measurable p hp ω T).comp (measurable_const.prodMk measurable_id)
  exact ((continuous_fst.inner continuous_snd).measurable.comp (measurable_id.prodMk hW)).add
    continuous_norm.measurable

theorem linearPolicyGap_smul (p : Policy Ω S (Feasible E 1)) (ω : Ω) (T : ℕ)
    {r : ℝ} (hr : 0 ≤ r) {u : E} (hu : ‖u‖ = 1) :
    linearPolicyGap p ω T (r • u) = r * (⟪linearPolicyOutput p r ω T u, u⟫_ℝ + 1) := by
  have he : linearPolicyOutput p 1 ω T (r • u) = linearPolicyOutput p r ω T u := by
    simp only [linearPolicyOutput, real_inner_smul_left, one_mul]
  rw [linearPolicyGap, he, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hr, hu, mul_one, real_inner_comm u (linearPolicyOutput p r ω T u)]
  ring

theorem gaussianAmbientRowLaw_adaptive_gap (p : Policy Ω S (Feasible E 1)) (hp : p.IsMeasurable)
    (ω : Ω) (T : ℕ) (hd : 86 ≤ Module.finrank ℝ E)
    (hT : (T : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 128) :
    3 / 4 ≤ (gaussianAmbientRowLaw E).real {a : E | 7 / 32 < linearPolicyGap p ω T a} := by
  let ρ := Measure.map (fun z : E => ‖z‖) (gaussianAmbientRowLaw E)
  let P := ρ.prod (sphericalLaw E)
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  letI : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (ρ.prod (sphericalLaw E)))
  let A : Set (ℝ × E) := Set.Ici (1 / 2) ×ˢ {u : E | ‖u‖ = 1}
  let B : Set (ℝ × E) := {z | -1 / 2 ≤ ⟪linearPolicyOutput p z.1 ω T z.2, z.2⟫_ℝ}
  have hangle : Measurable (fun z : ℝ × E => ⟪linearPolicyOutput p z.1 ω T z.2, z.2⟫_ℝ) :=
    (continuous_fst.inner continuous_snd).measurable.comp
      ((linearPolicyOutput_joint_measurable p hp ω T).prodMk measurable_snd)
  have hB : MeasurableSet B := measurableSet_le measurable_const hangle
  have hbad : P.real Bᶜ ≤ 1 / 8 := by
    apply product_probability_of_slice_bound ρ (sphericalLaw E) Bᶜ hB.compl (by norm_num)
    intro r
    simpa only [B, Set.preimage_compl, Set.preimage_setOf_eq, Set.compl_setOf, not_le] using
      linear_policy_output_tail_eighth p hp r ω T hd hT
  have hBprob : 7 / 8 ≤ P.real B := by
    have h := measureReal_add_measureReal_compl (μ := P) hB
    rw [measureReal_univ_eq_one] at h
    linarith
  have hunit : (sphericalLaw E).real {u : E | ‖u‖ = 1} = 1 := by
    calc
      _ = (sphericalLaw E).real Set.univ := by
        apply measureReal_congr
        filter_upwards [sphericalLaw_unit (E := E)] with u hu
        change (‖u‖ = 1) = True
        exact propext (iff_true_intro hu)
      _ = 1 := measureReal_univ_eq_one
  have hAprob : 7 / 8 ≤ P.real A := by
    change 7 / 8 ≤ (ρ.prod (sphericalLaw E)).real (Set.Ici (1 / 2) ×ˢ {u : E | ‖u‖ = 1})
    rw [measureReal_prod_prod, hunit, mul_one]
    dsimp only [ρ]
    rw [map_measureReal_apply continuous_norm.measurable measurableSet_Ici]
    exact gaussianAmbientRowLaw_norm_large hd
  have hinter : 3 / 4 ≤ P.real (A ∩ B) := by
    have h := measureReal_union_add_inter (μ := P) (s := A) hB
    have hu : P.real (A ∪ B) ≤ 1 := by
      simpa only [measureReal_univ_eq_one] using
        measureReal_mono (μ := P) (Set.subset_univ (A ∪ B)) (measure_ne_top _ _)
    linarith
  let C : Set (ℝ × E) := {z | 7 / 32 < linearPolicyGap p ω T (z.1 • z.2)}
  have hsub : A ∩ B ⊆ C := by
    rintro ⟨r, u⟩ ⟨⟨hr, hu⟩, hb⟩
    have hr' : (1 / 2 : ℝ) ≤ r := hr
    have hu' : ‖u‖ = 1 := hu
    have hb' : -1 / 2 ≤ ⟪linearPolicyOutput p r ω T u, u⟫_ℝ := hb
    change 7 / 32 < linearPolicyGap p ω T (r • u)
    rw [linearPolicyGap_smul p ω T (by linarith) hu']
    nlinarith
  have hs : MeasurableSet {a : E | 7 / 32 < linearPolicyGap p ω T a} :=
    measurableSet_lt measurable_const (linearPolicyGap_measurable p hp ω T)
  have hmap := congrArg (fun μ : Measure E => μ.real {a : E | 7 / 32 < linearPolicyGap p ω T a})
    (gaussianAmbientRowLaw_radial_reconstruct (E := E))
  try dsimp only at hmap
  rw [map_measureReal_apply (f := fun p : ℝ × E => p.1 • p.2) (measurable_fst.smul measurable_snd) hs] at hmap
  exact (hinter.trans (measureReal_mono hsub (measure_ne_top _ _))).trans_eq hmap

end
end Nonsmooth
