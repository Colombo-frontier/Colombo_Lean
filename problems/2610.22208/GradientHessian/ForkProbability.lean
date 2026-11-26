import GradientHessian.ForkColumns
import GradientHessian.ConditionedSource
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Probability ingredients of the chronological fork

Marks have the actual independent sphere-column law in orthonormal coordinates.
The branch-count expectation below uses one shared random input and independent
branch coordinates.  A branch event is evaluated only on that shared input and
its own coordinate; no conditional-independence assertion is assumed.
-/

namespace GradientHessian.ForkProbability

open Matrix MeasureTheory ProbabilityTheory LowRank
open GradientHessian.MatrixAnalyticNorms GradientHessian.SphereGaussian
open GradientHessian.SphereColumnNorm GradientHessian.ForkColumns
open scoped InnerProductSpace ENNReal BigOperators
noncomputable section

def embeddedMarks {d m r : ℕ} (B : Matrix (Fin d) (Fin m) ℝ)
    (z : Fin r → EuclideanSpace ℝ (Fin m)) : Fin r → EuclideanSpace ℝ (Fin d) :=
  fun i => matrixEuclideanMap B (z i)

theorem embeddedMarks_matrix {d m r : ℕ} (B : Matrix (Fin d) (Fin m) ℝ)
    (z : Fin r → EuclideanSpace ℝ (Fin m)) :
    columnMatrix (embeddedMarks B z) = B*columnMatrix z := by
  ext i j
  rfl

theorem embeddedMarks_opNorm_le {d m r : ℕ} (B : Matrix (Fin d) (Fin m) ℝ)
    (hB : Bᵀ*B = 1) (z : Fin r → EuclideanSpace ℝ (Fin m)) :
    ‖matrixEuclideanMap (columnMatrix (embeddedMarks B z))‖ ≤
      ‖matrixEuclideanMap (columnMatrix z)‖ := by
  have hb : ‖matrixEuclideanMap B‖ ≤ 1 :=
    matrix_norm_le_of_gram_le B zero_le_one (by
      simpa [hB, LoewnerLE] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef))
  rw [embeddedMarks_matrix, matrixEuclideanMap_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _))

theorem embeddedMarks_unit {d m r : ℕ} (hm : 0 < m)
    (B : Matrix (Fin d) (Fin m) ℝ) (hB : Bᵀ*B = 1) :
    ∀ᵐ z ∂columnLaw (EuclideanSpace ℝ (Fin m)) r, ∀ i, ‖embeddedMarks B z i‖ = 1 := by
  letI : NeZero m := ⟨hm.ne'⟩
  apply ae_all_iff.mpr
  intro i
  have h : ∀ᵐ z ∂columnLaw (EuclideanSpace ℝ (Fin m)) r, ‖z i‖ = 1 :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin r => sphereLaw (EuclideanSpace ℝ (Fin m)))
      (i := i)).eventually (sphereLaw_unit (E := EuclideanSpace ℝ (Fin m)))
  filter_upwards [h] with z hz
  exact (ReadoutMarks.mark_norm B hB (z i)).trans hz

theorem embeddedMarks_range {d m r : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin m) ℝ) (hPB : P*B = B)
    (z : Fin r → EuclideanSpace ℝ (Fin m)) (i : Fin r) :
    P *ᵥ ⇑(embeddedMarks B z i) = ⇑(embeddedMarks B z i) :=
  ReadoutMarks.mark_in_range P B hPB (z i)

/-- The source marks in an arbitrary orthonormal realization retain the
proved column-norm tail.  Here there are exactly `r` marks in dimension `r`. -/
theorem embeddedMarks_tail {d r : ℕ} (hr : 0 < r)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B = 1) :
    (columnLaw (EuclideanSpace ℝ (Fin r)) r).real
      {z | 4 < ‖matrixEuclideanMap (columnMatrix (embeddedMarks B z))‖} ≤
        Real.exp (-Real.log (3/2:ℝ)*(r:ℝ)) := by
  apply le_trans (measureReal_mono (fun z hz => hz.trans_le (embeddedMarks_opNorm_le B hB z)))
  exact manuscript_column_sphere_tail hr

section Branches

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

theorem map_pi_eval (ν : Measure Z) [IsProbabilityMeasure ν] {r : ℕ} (i : Fin r) :
    (Measure.pi (fun _ : Fin r => ν)).map (fun z => z i) = ν := by
  classical
  ext U hU
  rw [Measure.map_apply (measurable_pi_apply i) hU]
  change (Measure.pi (fun _ : Fin r => ν)) ((Function.eval i) ⁻¹' U) = ν U
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  simp only [Function.update_apply]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem map_shared_coordinate (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Z) [IsProbabilityMeasure ν] {r : ℕ} (i : Fin r) :
    (μ.prod (Measure.pi (fun _ : Fin r => ν))).map
      (fun p : Ω × (Fin r → Z) => (p.1,p.2 i)) = μ.prod ν := by
  have h := Measure.map_prod_map μ (Measure.pi (fun _ : Fin r => ν))
    measurable_id (measurable_pi_apply i)
  simpa only [Measure.map_id, map_pi_eval, Prod.map, id_eq] using h.symm

def hitCount {r : ℕ} (H : Set (Ω × Z)) (ω : Ω) (z : Fin r → Z) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => (ω,z i) ∈ H)).card

omit [MeasurableSpace Ω] [MeasurableSpace Z] in
theorem hitCount_eq_sum {r : ℕ} (H : Set (Ω × Z)) (ω : Ω) (z : Fin r → Z) :
    (hitCount H ω z : ℝ) = ∑ i, H.indicator (fun _ => (1:ℝ)) (ω,z i) := by
  classical
  rw [hitCount, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (ω,z i) ∈ H <;> simp [h, Set.indicator]

omit [MeasurableSpace Ω] [MeasurableSpace Z] in
theorem hitCount_le {r : ℕ} (H : Set (Ω × Z)) (ω : Ω) (z : Fin r → Z) :
    hitCount H ω z ≤ r := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin r))

theorem hitCount_measurable {r : ℕ} {H : Set (Ω × Z)} (hH : MeasurableSet H) :
    Measurable (fun p : Ω × (Fin r → Z) => (hitCount H p.1 p.2 : ℝ)) := by
  simp_rw [hitCount_eq_sum]
  apply Finset.measurable_sum
  intro i _
  exact (measurable_const.indicator hH).comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem hitCount_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Z) [IsProbabilityMeasure ν] {r : ℕ}
    {H : Set (Ω × Z)} (hH : MeasurableSet H) :
    Integrable (fun p : Ω × (Fin r → Z) => (hitCount H p.1 p.2 : ℝ))
      (μ.prod (Measure.pi (fun _ : Fin r => ν))) := by
  apply (integrable_const (r:ℝ)).mono' (hitCount_measurable hH).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hitCount_le H p.1 p.2)

/-- Exact expectation with a shared input and independent branch coordinates.
The event may depend arbitrarily on the shared input, including saved state. -/
theorem integral_hitCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Z) [IsProbabilityMeasure ν] (r : ℕ)
    {H : Set (Ω × Z)} (hH : MeasurableSet H) :
    (∫ p : Ω × (Fin r → Z), (hitCount H p.1 p.2 : ℝ)
      ∂μ.prod (Measure.pi (fun _ : Fin r => ν))) = (r:ℝ)*(μ.prod ν).real H := by
  classical
  let ρ := μ.prod (Measure.pi (fun _ : Fin r => ν))
  have hm (i : Fin r) : Measurable (fun p : Ω × (Fin r → Z) => (p.1,p.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hint (i : Fin r) : Integrable
      (fun p : Ω × (Fin r → Z) => H.indicator (fun _ => (1:ℝ)) (p.1,p.2 i)) ρ := by
    have hbase : Integrable (H.indicator (fun _ => (1:ℝ)))
        (ρ.map (fun p : Ω × (Fin r → Z) => (p.1,p.2 i))) := by
      rw [map_shared_coordinate μ ν i]
      exact (integrable_const (1:ℝ)).indicator hH
    exact hbase.comp_aemeasurable (hm i).aemeasurable
  simp_rw [hitCount_eq_sum]
  rw [integral_finset_sum _ (fun i _ => hint i)]
  have hi (i : Fin r) : (∫ p : Ω × (Fin r → Z),
      H.indicator (fun _ => (1:ℝ)) (p.1,p.2 i) ∂ρ) = (μ.prod ν).real H := by
    rw [← integral_map (hm i).aemeasurable
      ((measurable_const.indicator hH).aestronglyMeasurable), map_shared_coordinate μ ν i]
    exact integral_indicator_one hH
  simp_rw [hi]
  simp

omit [MeasurableSpace Ω] [MeasurableSpace Z] in
theorem hitCount_restrict {r : ℕ} (E : Set Ω) (H : Set (Ω × Z))
    (ω : Ω) (z : Fin r → Z) :
    (hitCount ((E ×ˢ Set.univ) ∩ H) ω z : ℝ) =
      E.indicator (fun ω => (hitCount H ω z : ℝ)) ω := by
  classical
  by_cases h : ω ∈ E
  · simp [hitCount, h]
  · simp [hitCount, h]

theorem integral_event_hitCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Z) [IsProbabilityMeasure ν] (r : ℕ)
    {E : Set Ω} (hE : MeasurableSet E) {H : Set (Ω × Z)} (hH : MeasurableSet H) :
    (∫ p : Ω × (Fin r → Z),
      E.indicator (fun ω => (hitCount H ω p.2 : ℝ)) p.1
      ∂μ.prod (Measure.pi (fun _ : Fin r => ν))) =
        (r:ℝ)*(μ.prod ν).real ((E ×ˢ Set.univ) ∩ H) := by
  simp_rw [← hitCount_restrict]
  exact integral_hitCount μ ν r ((hE.prod MeasurableSet.univ).inter hH)

/-- The source proof's exact identity `E[1_E H] = p_E r p_hit`, with
conditioning performed only on the shared input and with the original branch
law preserved. Positive event mass is stated explicitly. -/
theorem integral_event_hitCount_cond (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Z) [IsProbabilityMeasure ν] (r : ℕ)
    {E : Set Ω} (hE : MeasurableSet E) (hp : 0 < μ.real E)
    {H : Set (Ω × Z)} (hH : MeasurableSet H) :
    (∫ p : Ω × (Fin r → Z),
      E.indicator (fun ω => (hitCount H ω p.2 : ℝ)) p.1
      ∂μ.prod (Measure.pi (fun _ : Fin r => ν))) =
        μ.real E*(r:ℝ)*((cond μ E).prod ν).real H := by
  rw [integral_event_hitCount μ ν r hE hH]
  have hc := ConditionedSource.cond_real_apply (μ.prod ν)
    (hE.prod MeasurableSet.univ) H
  rw [ConditionedSource.condition_matrix_only μ ν hE] at hc
  have he : (μ.prod ν).real (E ×ˢ Set.univ) = μ.real E := by
    simp [measureReal_def, Measure.prod_prod]
  rw [he] at hc
  have hmul := (eq_div_iff hp.ne').mp hc
  rw [← hmul]
  ring

end Branches

section ExceptionalEvent

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integrating the deterministic trace implication loses at most `r` times
the actual exceptional-event probability. This lemma uses genuine integrals
and events; it has no independence hypothesis. -/
theorem integral_event_count_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E B : Set Ω} (hE : MeasurableSet E) (hB : MeasurableSet B)
    (H T : Ω → ℝ) (hH : Integrable H μ) (hT : Integrable T μ)
    {r γ : ℝ} (hr : 0 ≤ r) (hγ : 0 < γ)
    (hcap : ∀ᵐ ω ∂μ, H ω ≤ r) (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω)
    (htrace : ∀ᵐ ω ∂μ, ω ∈ E → ω ∉ B → γ^2*H ω/256 ≤ T ω) :
    (∫ ω, E.indicator H ω ∂μ) ≤
      (256/γ^2)*(∫ ω, T ω ∂μ) + r*μ.real B := by
  have hg : 0 < γ^2 := sq_pos_of_pos hγ
  have hfactor : 0 ≤ 256/γ^2 := by positivity
  have hbint : Integrable (B.indicator (fun _ => r)) μ := (integrable_const r).indicator hB
  have hm : (fun ω => E.indicator H ω) ≤ᵐ[μ]
      (fun ω => (256/γ^2)*T ω+B.indicator (fun _ => r) ω) := by
    filter_upwards [hcap,hT0,htrace] with ω hcap hT0 htrace
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      by_cases hb : ω ∈ B
      · rw [Set.indicator_of_mem hb]
        nlinarith [mul_nonneg hfactor hT0]
      · rw [Set.indicator_of_not_mem hb, add_zero]
        have ht := htrace he hb
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hg).mpr
        have hm : H ω*γ^2 ≤ 256*T ω := by linarith
        exact hm
    · rw [Set.indicator_of_not_mem he]
      exact add_nonneg (mul_nonneg hfactor hT0)
        (Set.indicator_nonneg (fun _ _ => hr) ω)
  have hineq := integral_mono_ae (hH.indicator hE)
    ((hT.const_mul (256/γ^2)).add hbint) hm
  change (∫ ω, E.indicator H ω ∂μ) ≤
    ∫ ω, (256/γ^2)*T ω+B.indicator (fun _ => r) ω ∂μ at hineq
  rw [integral_add (hT.const_mul (256/γ^2)) hbint, integral_const_mul,
    integral_indicator_const r hB, smul_eq_mul] at hineq
  simpa only [mul_comm (μ.real B) r] using hineq

end ExceptionalEvent
end
end GradientHessian.ForkProbability
