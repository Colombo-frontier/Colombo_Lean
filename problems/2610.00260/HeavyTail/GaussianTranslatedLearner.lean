import HeavyTail.GaussianStageLearner

/-! Translation identities for choosing a Gaussian learner once at center zero.
The same selected update is then used at every random stage center, avoiding
any assumption of joint measurability for center-indexed classical choices. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace HeavyTail.GaussianEntropy

universe u
variable {ι E : Type u} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem finiteMixtureMean_translate (c : E) (offsets : ι → E)
    {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    finiteMixtureMean (fun i => c + offsets i) w = c + finiteMixtureMean offsets w := by
  simp only [finiteMixtureMean_apply, smul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, hw.2, one_smul]

theorem finiteMixtureMean_translate_sub (c : E) (offsets : ι → E)
    {q w : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hw : w ∈ stdSimplex ℝ ι) :
    finiteMixtureMean (fun i => c + offsets i) (q - w) = finiteMixtureMean offsets (q - w) := by
  rw [map_sub, map_sub, finiteMixtureMean_translate c offsets hq,
    finiteMixtureMean_translate c offsets hw]
  abel

theorem observedComponentIntegrand_translate (c : E) (a η : ℝ) (offsets : ι → E)
    (i : ι) (Y : E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) (z : E) :
    observedComponentIntegrand E c a η (fun i => c + offsets i) i (Y, w) z =
      observedComponentIntegrand E 0 a η offsets i (Y, w) z := by
  have hm : c + a • z - finiteMixtureMean (fun i => c + offsets i) w =
      a • z - finiteMixtureMean offsets w := by
    rw [finiteMixtureMean_translate c offsets hw]
    abel
  simp only [observedComponentIntegrand, hm, add_sub_cancel_left, sub_zero, zero_add]

theorem observedClippedLoss_translate (c : E) (a η : ℝ) (offsets : ι → E)
    (Y : E) {w : ι → ℝ} (hw : w ∈ stdSimplex ℝ ι) :
    observedClippedLoss E c a η (fun i => c + offsets i) (Y, w) =
      observedClippedLoss E 0 a η offsets (Y, w) := by
  unfold observedClippedLoss
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (observedComponentIntegrand_translate c a η offsets i Y hw)

theorem gaussianOnlineDerivative_translate_diff (c : E) (a β : ℝ) (offsets : ι → E)
    {q p w : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hw : w ∈ stdSimplex ℝ ι) :
    (gaussianOnlineDerivative E c a β (fun i => c + offsets i) p -
      gaussianOnlineDerivative E c a β (fun i => c + offsets i) w) (q - p) =
    (gaussianOnlineDerivative E 0 a β offsets p -
      gaussianOnlineDerivative E 0 a β offsets w) (q - p) := by
  simp only [gaussianOnlineDerivative, gaussianMixtureGeneratorDerivative,
    meanRegularizedEntropyDerivative, add_sub_cancel_left, sub_zero,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply,
    finiteMixtureMean_translate_sub c offsets hq hp,
    finiteMixtureMean_translate c offsets hp, finiteMixtureMean_translate c offsets hw,
    inner_add_left, smul_eq_mul]
  ring

theorem translatedGaussianUpdate_first_order (c : E) (a η β : ℝ) (offsets : ι → E)
    {ε : ℝ} (hε : 0 < ε) (Y : E) (w : SimplexPoint ι)
    {q : ι → ℝ} (hq : q ∈ stdSimplex ℝ ι) :
    let p := gaussianOnlineUpdate E 0 a η β offsets hε (w, Y);
    -ε ≤ (observedClippedLoss E c a η (fun i => c + offsets i) (Y, w.val) +
      gaussianOnlineDerivative E c a β (fun i => c + offsets i) p.val -
      gaussianOnlineDerivative E c a β (fun i => c + offsets i) w.val) (q - p.val) := by
  dsimp only
  let p := gaussianOnlineUpdate E 0 a η β offsets hε (w, Y)
  have hf := (gaussian_observation_update_exists E 0 a η β offsets hε).choose_spec.2
    (Y, w) q hq
  change -ε ≤ (observedClippedLoss E 0 a η offsets (Y, w.val) +
    gaussianOnlineDerivative E 0 a β offsets p.val -
    gaussianOnlineDerivative E 0 a β offsets w.val) (q - p.val) at hf
  change -ε ≤ (observedClippedLoss E c a η (fun i => c + offsets i) (Y, w.val) +
    gaussianOnlineDerivative E c a β (fun i => c + offsets i) p.val -
    gaussianOnlineDerivative E c a β (fun i => c + offsets i) w.val) (q - p.val)
  rw [observedClippedLoss_translate c a η offsets Y w.property]
  have hd := gaussianOnlineDerivative_translate_diff c a β offsets hq p.property w.property
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] at hf hd ⊢
  linarith only [hf, hd]

def translatedGaussianStageLearner (c : E) {R : ℝ} (a η β : ℝ) (offsets : ι → E)
    (hball : ∀ i, ‖offsets i‖ ≤ R) (initial : SimplexPoint ι)
    {ε : ℝ} (hε : 0 < ε) : StageLearner (SimplexPoint ι) E c R where
  initial := initial
  point w := c + finiteMixtureMean offsets w.val
  point_measurable := measurable_const.add
    ((finiteMixtureMean offsets).continuous.measurable.comp measurable_subtype_coe)
  point_bound w := by
    have hb := finiteMixtureMean_ball E (0 : E) R offsets
      (by simpa only [sub_zero] using hball) w.property
    simpa only [add_sub_cancel_left, sub_zero] using hb
  update := gaussianOnlineUpdate E 0 a η β offsets hε
  update_measurable := gaussianOnlineUpdate_measurable E 0 a η β offsets hε

theorem translatedGaussianPoint_measurable (offsets : ι → E) :
    Measurable (fun p : E × SimplexPoint ι => p.1 + finiteMixtureMean offsets p.2.val) :=
  measurable_fst.add ((finiteMixtureMean offsets).continuous.measurable.comp
    (measurable_subtype_coe.comp measurable_snd))

end HeavyTail.GaussianEntropy
