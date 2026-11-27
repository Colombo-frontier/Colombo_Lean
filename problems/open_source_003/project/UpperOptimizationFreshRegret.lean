import UpperOptimizationFresh

/-! Integrating actual fresh-block estimators at adaptive past-dependent states. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace Task006.Full

section Fresh
variable {T : ℕ} {B E : Type*} [MeasurableSpace B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (ν : Measure B) [IsProbabilityMeasure ν]
  (t : Fin T) (X : (Fin T → B) → E) (hX : Measurable X)
  (hpast : ∀ w w', (∀ j : Fin T, j.val < t.val → w j = w' j) → X w = X w')

include hX hpast

/-- Fixed-state mean bias becomes the correct expected subgradient inequality
for the genuine adaptive state, by proved fresh-coordinate independence. -/
theorem fresh_expected_subgradient_le
    {K : Set E} (hK : MeasurableSet K) (hfeas : ∀ w, X w ∈ K)
    (g : E → B → E) (hg : Measurable (Function.uncurry g))
    (f : E → ℝ) (hf : Measurable f) (v : E → E) (z : E)
    {C β : ℝ} (hC : 0 ≤ C)
    (hgi : ∀ x ∈ K, Integrable (g x) ν)
    (hbias : ∀ x ∈ K, ‖(∫ b, g x b ∂ν) - v x‖ ≤ β)
    (hsub : ∀ x ∈ K, f x - f z ≤ inner ℝ (x - z) (v x))
    (hdisp : ∀ x ∈ K, ‖x - z‖ ≤ C)
    (hgap : Integrable (fun w => f (X w) - f z) (Measure.pi (fun _ : Fin T => ν)))
    (hprod : Integrable (fun p : E × B => inner ℝ (p.1 - z) (g p.1 p.2))
      (((Measure.pi (fun _ : Fin T => ν)).map X).prod ν)) :
    (∫ w, f (X w) - f z ∂Measure.pi (fun _ : Fin T => ν)) ≤
      (∫ w, inner ℝ (X w - z) (g (X w) (w t)) ∂Measure.pi (fun _ : Fin T => ν)) + C * β := by
  let stateLaw : Measure E := (Measure.pi (fun _ : Fin T => ν)).map X
  letI hState : IsProbabilityMeasure stateLaw := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hsupport : ∀ᵐ x ∂stateLaw, x ∈ K := by
    exact (ae_map_iff hX.aemeasurable hK).mpr (Filter.Eventually.of_forall hfeas)
  have hHm : Measurable (fun p : E × B => inner ℝ (p.1 - z) (g p.1 p.2)) :=
    (measurable_fst.sub measurable_const).inner hg
  have hfresh := fresh_block_integral ν t X hX hpast _ hHm hprod
  have hgapState : Integrable (fun x => f x - f z) stateLaw := by
    exact (integrable_map_measure (hf.sub measurable_const).aestronglyMeasurable hX.aemeasurable).mpr hgap
  have hpoint : ∀ᵐ x ∂stateLaw, f x - f z ≤
      (∫ b, inner ℝ (x - z) (g x b) ∂ν) + C * β := by
    filter_upwards [hsupport] with x hx
    rw [integral_inner (hgi x hx)]
    have hb : ‖v x - (∫ b, g x b ∂ν)‖ ≤ β := by
      rw [norm_sub_rev]
      exact hbias x hx
    have he := (real_inner_le_norm (x - z) (v x - ∫ b, g x b ∂ν)).trans
      (mul_le_mul (hdisp x hx) hb (norm_nonneg _) hC)
    rw [inner_sub_right] at he
    linarith [hsub x hx]
  have hm := integral_mono_ae hgapState
    (hprod.integral_prod_left.add (integrable_const (C * β))) hpoint
  have hadd := integral_add hprod.integral_prod_left (integrable_const (C * β))
  simp only [Pi.add_apply, Prod.fst, Prod.snd] at hm hadd hfresh
  rw [hadd] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  have heq : (∫ w, f (X w) - f z ∂Measure.pi (fun _ : Fin T => ν)) =
      ∫ x, f x - f z ∂stateLaw :=
    (integral_map hX.aemeasurable (hf.sub (measurable_const (a := f z))).aestronglyMeasurable).symm
  rw [heq, hfresh]
  exact hm

theorem fresh_second_moment_le
    {K : Set E} (hK : MeasurableSet K) (hfeas : ∀ w, X w ∈ K)
    (g : E → B → E) (hg : Measurable (Function.uncurry g)) {W : ℝ}
    (hW : ∀ x ∈ K, (∫ b, ‖g x b‖ ^ 2 ∂ν) ≤ W)
    (hprod : Integrable (fun p : E × B => ‖g p.1 p.2‖ ^ 2)
      (((Measure.pi (fun _ : Fin T => ν)).map X).prod ν)) :
    (∫ w, ‖g (X w) (w t)‖ ^ 2 ∂Measure.pi (fun _ : Fin T => ν)) ≤ W := by
  have hfresh := fresh_block_integral ν t X hX hpast _ (hg.norm.pow_const 2) hprod
  simp only [Function.uncurry] at hfresh
  rw [hfresh]
  have hs : ∀ᵐ x ∂(Measure.pi (fun _ : Fin T => ν)).map X, x ∈ K := by
    exact (ae_map_iff hX.aemeasurable hK).mpr (Filter.Eventually.of_forall hfeas)
  letI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin T => ν)).map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hm := integral_mono_ae hprod.integral_prod_left (integrable_const W)
    (hs.mono (fun x hx => hW x hx))
  simpa only [integral_const, probReal_univ, one_smul] using hm

end Fresh

#print axioms fresh_expected_subgradient_le
#print axioms fresh_second_moment_le

end Task006.Full
