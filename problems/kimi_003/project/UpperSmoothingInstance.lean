import UpperSmoothingTranslation

/-!
Closing the analytic bridge for the actual local sample-instance model.
The global Lipschitz extension is used only in the proof. The implemented
algorithm still queries the original sample function at its original points.
-/

open MeasureTheory Metric Set Filter InnerProductSpace
open scoped Topology NNReal

namespace Task006.Full

@[simp] theorem space_finrank (d : ℕ) : Module.finrank ℝ (Space d) = d := by
  simp [Space]

noncomputable def ballSmoothGradient {d : ℕ} (f : Space d → ℝ) (ρ : ℝ) (x : Space d) : Space d :=
  (toDual ℝ (Space d)).symm (ballSmoothDerivative f ρ x)

theorem ballSmooth_hasGradientAt_global {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) (x : Space d) :
    HasGradientAt (ballSmooth f ρ) (ballSmoothGradient f ρ x) x :=
  (hasFDerivAt_iff_hasGradientAt).mp (ballSmooth_hasFDerivAt_global hf hρ x).2

noncomputable def smoothGradientConstant (d : ℕ) (L : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) : ℝ≥0 :=
  ⟨2 * (Module.finrank ℝ (Space d) : ℝ) * L / ρ, by positivity⟩

theorem ballSmoothGradient_lipschitz {d : ℕ} {f : Space d → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ)
    (hn : 1 ≤ Module.finrank ℝ (Space d)) :
    LipschitzWith (smoothGradientConstant d L ρ hρ.le) (ballSmoothGradient f ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heq := (toDual ℝ (Space d)).symm.dist_map
    (ballSmoothDerivative f ρ x) (ballSmoothDerivative f ρ y)
  change dist ((toDual ℝ (Space d)).symm (ballSmoothDerivative f ρ x))
    ((toDual ℝ (Space d)).symm (ballSmoothDerivative f ρ y)) ≤ _
  rw [heq, dist_eq_norm, dist_eq_norm]
  exact norm_ballSmoothDerivative_sub_le hf hρ hn x y

namespace SampleInstance

variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- McShane's extension is an auxiliary mathematical object, not an oracle. -/
noncomputable def objectiveExtension (hL : 0 ≤ L) (hR : 0 ≤ R) : Space d → ℝ :=
  Classical.choose (I.objective_lipschitzOn hL hR).extend_real

theorem objectiveExtension_lipschitz (hL : 0 ≤ L) (hR : 0 ≤ R) :
    LipschitzWith ⟨L, hL⟩ (I.objectiveExtension hL hR) :=
  (Classical.choose_spec (I.objective_lipschitzOn hL hR).extend_real).1

theorem objectiveExtension_eq (hL : 0 ≤ L) (hR : 0 ≤ R) :
    EqOn I.objective (I.objectiveExtension hL hR) (queryDomain d R) :=
  (Classical.choose_spec (I.objective_lipschitzOn hL hR).extend_real).2

theorem ballSmooth_eq_extension (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) {x : Space d} (hx : ‖x‖ ≤ R) :
    ballSmooth I.objective ρ x = ballSmooth (I.objectiveExtension hL hR) ρ x := by
  apply integral_congr_ae
  filter_upwards [unitBallLaw_norm_le d] with u hu
  exact I.objectiveExtension_eq hL hR (ballTranslate_mem_queryDomain hρ hρR hx hu)

noncomputable def smoothedGradient (hL : 0 ≤ L) (hR : 0 ≤ R) (ρ : ℝ) (x : Space d) : Space d :=
  ballSmoothGradient (I.objectiveExtension hL hR) ρ x

/-- Differentiability on the exact inner neighborhood of the actual objective.
The equality to the extension holds in a neighborhood, so no boundary or
sample smoothness hypothesis is added to the problem. -/
theorem ballSmooth_hasGradientAt (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ ≤ R) {x : Space d} (hx : ‖x‖ < R) :
    HasGradientAt (ballSmooth I.objective ρ) (I.smoothedGradient hL hR ρ x) x := by
  have hext := ballSmooth_hasGradientAt_global (I.objectiveExtension_lipschitz hL hR) hρ x
  have heq : ballSmooth I.objective ρ =ᶠ[𝓝 x]
      ballSmooth (I.objectiveExtension hL hR) ρ := by
    have hmem : x ∈ ball (0 : Space d) R := by simpa using hx
    filter_upwards [isOpen_ball.mem_nhds hmem] with y hy
    have hyn : ‖y‖ < R := by simpa using hy
    exact I.ballSmooth_eq_extension hL hR hρ.le hρR hyn.le
  exact hext.congr_of_eventuallyEq heq

theorem smoothedGradient_lipschitz (hL : 0 ≤ L) (hR : 0 ≤ R) {ρ : ℝ}
    (hρ : 0 < ρ) (hn : 1 ≤ Module.finrank ℝ (Space d)) :
    LipschitzWith (smoothGradientConstant d ⟨L, hL⟩ ρ hρ.le) (I.smoothedGradient hL hR ρ) :=
  ballSmoothGradient_lipschitz (I.objectiveExtension_lipschitz hL hR) hρ hn

/-- The actual sample-instance central finite-difference bias. This uses the
proved conservative factor `2d` and therefore gives `d L δ / ρ`, twice the
manuscript's sharper intermediate bound, with the main accuracy still intact. -/
theorem centralSecant_smoothedGradient_error (hL : 0 ≤ L) (hR : 0 ≤ R)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) (hδ : 0 < δ) (hd : 1 ≤ d)
    {x q : Space d} (hx : ‖x‖ ≤ R - (ρ + δ)) (hq : ‖q‖ ≤ 1) :
    |centralSecant (ballSmooth I.objective ρ) x q δ -
        inner ℝ (I.smoothedGradient hL hR ρ x) q| ≤ d * L * δ / ρ := by
  have hpath : ∀ t ∈ Icc (-δ) δ, x + t • q ∈ ball (0 : Space d) R := by
    intro t ht
    have habs : |t| ≤ δ := abs_le.mpr ht
    have hsmul : ‖t • q‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg t, norm_nonneg q]
    have hnorm := norm_add_le x (t • q)
    have : ‖x + t • q‖ < R := by linarith
    simpa using this
  have hgrad : ∀ y ∈ ball (0 : Space d) R,
      HasFDerivAt (ballSmooth I.objective ρ) (innerSL ℝ (I.smoothedGradient hL hR ρ y)) y := by
    intro y hy
    have hyn : ‖y‖ < R := by simpa using hy
    convert! (I.ballSmooth_hasGradientAt hL hR hρ hρR hyn).hasFDerivAt using 1
  have hn : 1 ≤ Module.finrank ℝ (Space d) := by simpa using hd
  have hs := centralSecant_error hδ hq
    (I.smoothedGradient_lipschitz hL hR hρ hn).lipschitzOnWith hgrad hpath
  change |centralSecant (ballSmooth I.objective ρ) x q δ -
    inner ℝ (I.smoothedGradient hL hR ρ x) q| ≤
      (2 * (Module.finrank ℝ (Space d) : ℝ) * L / ρ) * δ / 2 at hs
  rw [space_finrank] at hs
  convert hs using 1 <;> ring

end SampleInstance

#print axioms SampleInstance.ballSmooth_hasGradientAt
#print axioms SampleInstance.smoothedGradient_lipschitz
#print axioms SampleInstance.centralSecant_smoothedGradient_error

end Task006.Full
