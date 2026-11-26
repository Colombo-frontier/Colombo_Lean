import FreshGradientMinimax.PathAuxiliary
import FreshGradientMinimax.GaussianOracleLaw

/-! Measurability and visible-coordinate dependence of the auxiliary oracle.
These hold even for coordinate lists with collisions; no global frame test is
allowed to influence the auxiliary trajectory. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open scoped InnerProductSpace InnerProduct

theorem linearFlatEnergy_continuous {n dy : ℕ} (A : Euclid dy →L[ℝ] Euclid n)
    (β : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : Continuous (linearFlatEnergy A β δ) :=
  continuous_iff_continuousAt.mpr (fun x => (linearFlatEnergy_hasFDerivAt A β hδ x).continuousAt)

theorem linearFlatGradient_continuous {n dy : ℕ} (A : Euclid dy →L[ℝ] Euclid n)
    (β : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : Continuous (linearFlatGradient A β δ) :=
  ((A†).continuous.comp ((flatSlope_lipschitz hδ).continuous.comp A.continuous)).const_smul β

theorem radialCapGradient_continuous {dy : ℕ} {Q : Euclid dy → ℝ} {G : Euclid dy → Euclid dy}
    (hQ : Continuous Q) (hG : Continuous G) {β R : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    Continuous (radialCapGradient Q G β R) := by
  have hw : Continuous (radialWall (E := Euclid dy) β R) :=
    continuous_iff_continuousAt.mpr (fun x => (radialWall_hasFDerivAt β R x).continuousAt)
  have hc : Continuous (radialCapWeight Q β R) :=
    (smoothRampSlope_lipschitz (by positivity : 0 < β * R ^ 2)).continuous.comp (hw.sub hQ)
  exact ((continuous_const.sub hc).smul hG).add (hc.smul (continuous_id.const_smul (8 * β)))

theorem auxiliaryPathCapGradient_measurable {n dy : ℕ} (C : Euclid dy →L[ℝ] Euclid n)
    {β δ R : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hR : 0 < R) (w : ℕ) :
    Measurable (auxiliaryPathCapGradient C β δ R w) := by
  apply Measurable.ite (isOpen_lt continuous_const continuous_norm).measurableSet
  · exact (continuous_id.const_smul (8 * β)).measurable
  · exact (radialCapGradient_continuous
      (linearFlatEnergy_continuous _ β hδ) (linearFlatGradient_continuous _ β hδ) hβ hR).measurable

theorem pathAuxiliaryReply_measurable (p : Parameters) (N : ℕ) {dy : ℕ}
    (C : Euclid dy →L[ℝ] Euclid (4 * N + 4)) (u v : Euclid dy) (t : ℕ) :
    Measurable (pathAuxiliaryReply p N C u v t) := by
  have hL : 0 < p.L := lt_of_lt_of_le p.μ_pos p.μ_le_L
  have hx : Measurable (fun z : Joint 1 dy => realCoord z.1) := by
    simpa only [Function.comp_def, realCoordCLM_apply] using
      realCoordCLM.continuous.measurable.comp (measurable_fst : Measurable (@Prod.fst (Euclid 1) (Euclid dy)))
  have hi : Measurable (fun z : Joint 1 dy => ⟪u, z.2⟫_ℝ) :=
    (innerSL ℝ u).continuous.measurable.comp measurable_snd
  have hg : Measurable (fun z : Joint 1 dy => auxiliaryPathCapGradient C (p.L / 8192)
      (pathHardFlatWidth p.L p.μ p.ε (4 * N + 3))
      (pathHardRadius p.L p.μ p.ε (4 * N + 3)) (t + 2) z.2) :=
    (auxiliaryPathCapGradient_measurable C (by positivity : 0 < p.L / 8192)
      (pathHardFlatWidth_pos hL p.μ_pos p.ε_pos (4 * N + 3)).le
      (pathHardRadius_pos hL p.μ_pos p.ε_pos (4 * N + 3)) (t + 2)).comp measurable_snd
  exact (realVector_continuous.measurable.comp
    (((measurable_const.mul hx).add measurable_const).add (measurable_const.mul hi))).prodMk
      (((((measurable_const.mul hx).smul measurable_const).sub
        (measurable_const.smul measurable_snd)).sub hg).add measurable_const)

theorem masked_coordinates_congr {n dy : ℕ} {C D : Euclid dy →L[ℝ] Euclid n}
    (S : Finset (Fin n)) (h : ∀ i ∈ S, ∀ y, C y i = D y i) :
    (coordinateMask S).comp C = (coordinateMask S).comp D := by
  apply ContinuousLinearMap.ext
  intro y
  ext i
  simp only [ContinuousLinearMap.comp_apply, coordinateMask_apply]
  split_ifs with hi
  · exact h i hi y
  · rfl

theorem auxiliaryPathCapGradient_congr {n dy : ℕ} {C D : Euclid dy →L[ℝ] Euclid n}
    (w : ℕ) (h : ∀ i ∈ pathVisible n w, ∀ y, C y i = D y i) (β δ R : ℝ) :
    auxiliaryPathCapGradient C β δ R w = auxiliaryPathCapGradient D β δ R w := by
  have he := masked_coordinates_congr _ h
  unfold auxiliaryPathCapGradient truncatedPathOperator
  rw [he]

theorem pathAuxiliaryReply_congr (p : Parameters) (N : ℕ) {dy : ℕ}
    {C D : Euclid dy →L[ℝ] Euclid (4 * N + 4)} (u v : Euclid dy) (t : ℕ)
    (h : ∀ i ∈ pathVisible (4 * N + 4) (t + 2), ∀ y, C y i = D y i) :
    pathAuxiliaryReply p N C u v t = pathAuxiliaryReply p N D u v t := by
  unfold pathAuxiliaryReply
  rw [auxiliaryPathCapGradient_congr (t + 2) h]

end FreshGradientMinimax
