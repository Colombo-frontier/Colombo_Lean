import UpperSmoothingInstance

/-! The sharp dL/rho gradient bound uses a midpoint common ball. Its half
radius loss cancels the two translated-set losses. No divergence formula or
unproved surface identity is a premise. -/
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Metric Set
open scoped NNReal
namespace Task006.Full

/-- A midpoint common ball halves the radial loss in each translated ball. -/
theorem norm_ballIntegral_sub_le_midpoint_shell {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Space d → V} {L ρ : ℝ}
    (hg : AEStronglyMeasurable g volume) (hbound : ∀ᵐ z, ‖g z‖ ≤ L)
    (x y : Space d) :
    ‖(∫ z in closedBall x ρ, g z) - (∫ z in closedBall y ρ, g z)‖ ≤
      2 * L * (volume.real (closedBall (0 : Space d) ρ) -
        volume.real (closedBall (0 : Space d) (ρ - ‖x - y‖ / 2))) := by
  let m := (1/2:ℝ) • (x+y)
  have hmx : dist m x = ‖x-y‖/2 := by
    have heq : m-x = (1/2:ℝ) • (y-x) := by dsimp [m]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2),
      norm_sub_rev]
    ring
  have hmy : dist m y = ‖x-y‖/2 := by
    have heq : m-y = (1/2:ℝ) • (x-y) := by dsimp [m]; module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    ring
  have hCA : closedBall m (ρ-‖x-y‖/2) ⊆ closedBall x ρ :=
    closedBall_subset_closedBall' (by rw [hmx]; linarith)
  have hCB : closedBall m (ρ-‖x-y‖/2) ⊆ closedBall y ρ :=
    closedBall_subset_closedBall' (by rw [hmy]; linarith)
  have hb := bounded_setIntegral_sub_common hg hbound
    (A := closedBall x ρ) (B := closedBall y ρ) (C := closedBall m (ρ-‖x-y‖/2))
    measure_closedBall_lt_top measure_closedBall_lt_top measurableSet_closedBall hCA hCB
  rw [addHaar_real_closedBall_center volume x ρ, addHaar_real_closedBall_center volume y ρ,
    addHaar_real_closedBall_center volume m (ρ-‖x-y‖/2)] at hb
  convert hb using 1 <;> ring

/-- The exact manuscript dL/rho bound, derived by actual uniform-ball
integration and the midpoint geometry above. -/
theorem norm_ballSmoothDerivative_sub_le_sharp {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ)
    (hn : 1 ≤ Module.finrank ℝ (Space d)) (x y : Space d) :
    ‖ballSmoothDerivative f ρ x - ballSmoothDerivative f ρ y‖ ≤
      ((Module.finrank ℝ (Space d) : ℝ) * L / ρ) * ‖x-y‖ := by
  let Vρ := volume.real (closedBall (0 : Space d) ρ)
  have hV : 0 < Vρ := ENNReal.toReal_pos
    (measure_closedBall_pos volume (0 : Space d) hρ).ne' measure_closedBall_lt_top.ne
  have hnreal : (1:ℝ) ≤ Module.finrank ℝ (Space d) := by exact_mod_cast hn
  by_cases hsmall : ‖x-y‖ ≤ 2*ρ
  · have hbound : ∀ᵐ z : Space d, ‖fderiv ℝ f z‖ ≤ L :=
      ae_of_all _ (fun _ => norm_fderiv_le_of_lipschitz ℝ hf)
    have hs := norm_ballIntegral_sub_le_midpoint_shell (ρ := ρ) (measurable_fderiv ℝ f).aestronglyMeasurable
      hbound x y
    have hv := ball_volume_loss_le (d := d) hρ (show 0 ≤ ‖x-y‖/2 by positivity)
      (show ‖x-y‖/2 ≤ ρ by linarith)
    rw [ballSmoothDerivative_ballIntegral f hρ x, ballSmoothDerivative_ballIntegral f hρ y,
      ← smul_sub ((volume.real (closedBall (0 : Space d) ρ))⁻¹)
        (∫ z in closedBall x ρ, fderiv ℝ f z) (∫ z in closedBall y ρ, fderiv ℝ f z),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hV)]
    have hmul := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hV.le)
    change Vρ⁻¹ * ‖(∫ z in closedBall x ρ, fderiv ℝ f z) -
      (∫ z in closedBall y ρ, fderiv ℝ f z)‖ ≤ _
    calc
      _ ≤ Vρ⁻¹*(2*L*(Vρ-volume.real (closedBall (0 : Space d) (ρ-‖x-y‖/2)))) := hmul
      _ ≤ Vρ⁻¹*(2*L*((Module.finrank ℝ (Space d):ℝ)*((‖x-y‖/2)/ρ)*Vρ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (by positivity))
          (inv_nonneg.mpr hV.le)
      _ = _ := by
        field_simp [hV.ne', hρ.ne']
        <;> ring
  · have hlarge : 2*ρ ≤ ‖x-y‖ := le_of_not_ge hsmall
    have hb := (norm_sub_le (ballSmoothDerivative f ρ x) (ballSmoothDerivative f ρ y)).trans
      (add_le_add (ballSmoothDerivative_norm_le hf ρ x) (ballSmoothDerivative_norm_le hf ρ y))
    have hr : (2:ℝ) ≤ ‖x-y‖/ρ := (le_div_iff₀ hρ).2 (by linarith)
    have hscale : (2:ℝ) ≤ (Module.finrank ℝ (Space d):ℝ)*(‖x-y‖/ρ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) (show 0 ≤ ‖x-y‖/ρ by positivity)]
    have hm := mul_le_mul_of_nonneg_left hscale L.coe_nonneg
    have hid : (L:ℝ)*((Module.finrank ℝ (Space d):ℝ)*(‖x-y‖/ρ)) =
        ((Module.finrank ℝ (Space d):ℝ)*L/ρ)*‖x-y‖ := by ring
    rw [hid] at hm
    linarith

noncomputable def sharpSmoothGradientConstant (d : ℕ) (L : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) : ℝ≥0 :=
  ⟨(Module.finrank ℝ (Space d):ℝ)*L/ρ, by positivity⟩

theorem ballSmoothGradient_lipschitz_sharp {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ)
    (hn : 1 ≤ Module.finrank ℝ (Space d)) :
    LipschitzWith (sharpSmoothGradientConstant d L ρ hρ.le) (ballSmoothGradient f ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heq := (InnerProductSpace.toDual ℝ (Space d)).symm.dist_map
    (ballSmoothDerivative f ρ x) (ballSmoothDerivative f ρ y)
  change dist ((InnerProductSpace.toDual ℝ (Space d)).symm (ballSmoothDerivative f ρ x))
    ((InnerProductSpace.toDual ℝ (Space d)).symm (ballSmoothDerivative f ρ y)) ≤ _
  rw [heq, dist_eq_norm, dist_eq_norm]
  exact norm_ballSmoothDerivative_sub_le_sharp hf hρ hn x y

namespace SampleInstance
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

theorem smoothedGradient_lipschitz_sharp (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ : ℝ}
    (hρ : 0 < ρ) (hn : 1 ≤ Module.finrank ℝ (Space d)) :
    LipschitzWith (sharpSmoothGradientConstant d ⟨L,hL⟩ ρ hρ.le) (I.smoothedGradient hL hR ρ) :=
  ballSmoothGradient_lipschitz_sharp (I.objectiveExtension_lipschitz hL hR) hρ hn

/-- Exact source U2 scalar constant, with the required one-half factor. -/
theorem centralSecant_smoothedGradient_error_sharp (hL : 0 ≤ L) (hR : 0 ≤ R)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) (hd : 1 ≤ d)
    {x q : Space d} (hx : ‖x‖ ≤ R-(ρ+δ)) (hq : ‖q‖ ≤ 1) :
    |centralSecant (ballSmooth I.objective ρ) x q δ -
      inner ℝ (I.smoothedGradient hL hR ρ x) q| ≤ d*L*δ/(2*ρ) := by
  have hpath : ∀ t ∈ Icc (-δ) δ, x+t•q ∈ ball (0:Space d) R := by
    intro t ht
    have habs : |t| ≤ δ := abs_le.mpr ht
    have hsmul : ‖t•q‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg t, norm_nonneg q]
    have hnorm := norm_add_le x (t•q)
    have : ‖x+t•q‖ < R := by linarith
    simpa using this
  have hgrad : ∀ y ∈ ball (0:Space d) R,
      HasFDerivAt (ballSmooth I.objective ρ) (innerSL ℝ (I.smoothedGradient hL hR ρ y)) y := by
    intro y hy
    have hyn : ‖y‖ < R := by simpa using hy
    convert! (I.ballSmooth_hasGradientAt hL hR hρ hρR hyn).hasFDerivAt using 1
  have hn : 1 ≤ Module.finrank ℝ (Space d) := by simpa using hd
  have hs := centralSecant_error hδ hq
    (I.smoothedGradient_lipschitz_sharp hL hR hρ hn).lipschitzOnWith hgrad hpath
  change |centralSecant (ballSmooth I.objective ρ) x q δ -
    inner ℝ (I.smoothedGradient hL hR ρ x) q| ≤
      ((Module.finrank ℝ (Space d):ℝ)*L/ρ)*δ/2 at hs
  rw [space_finrank] at hs
  convert hs using 1 <;> ring

end SampleInstance

end Task006.Full
