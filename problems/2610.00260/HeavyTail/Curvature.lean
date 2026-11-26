import HeavyTail.Envelope
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace HeavyTail
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The composite objective has the strong-convexity modulus of its regularizer. -/
theorem composite_strongConvexOn {S : Set E} {f r : E → ℝ} {μ : ℝ}
    (hf : ConvexOn ℝ S f) (hr : StrongConvexOn S μ r) :
    StrongConvexOn S μ (fun x => f x + r x) := by
  simpa only [Pi.zero_apply, zero_add, Pi.add_apply] using hf.uniformConvexOn_zero.add hr

/-- Equation `eq:growth`, from actual strong convexity and minimality. -/
theorem strongConvex_minimum_growth {S : Set E} {F : E → ℝ} {μ : ℝ} {xstar x : E}
    (hμ : 0 ≤ μ) (hF : StrongConvexOn S μ F) (hstar : xstar ∈ S) (hx : x ∈ S)
    (hmin : ∀ y ∈ S, F xstar ≤ F y) :
    μ / 2 * ‖x - xstar‖ ^ 2 ≤ F x - F xstar := by
  let g := μ / 2 * ‖x - xstar‖ ^ 2
  let d := F x - F xstar
  have hd : 0 ≤ d := sub_nonneg.mpr (hmin x hx)
  have hg : 0 ≤ g := by dsimp [g]; positivity
  change g ≤ d
  by_contra h
  have hgd : d < g := lt_of_not_ge h
  have hg0 : 0 < g := lt_of_le_of_lt hd hgd
  let t := (g - d) / (2 * g)
  have ht : 0 < t := div_pos (sub_pos.mpr hgd) (by positivity)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * g)).mpr
    linarith
  have htID : t * g = (g - d) / 2 := by dsimp [t]; field_simp; ring
  have hy : (1 - t) • xstar + t • x ∈ S :=
    hF.1 hstar hx (by linarith) ht.le (by ring)
  have hc := hF.2 hstar hx (by linarith : 0 ≤ 1 - t) ht.le (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, norm_sub_rev xstar x] at hc
  have hm := hmin _ hy
  have hscaled : t * ((1 - t) * g) ≤ t * d := by
    dsimp [g, d]
    nlinarith
  have hgrow : (1 - t) * g ≤ d := (mul_le_mul_left ht).mp hscaled
  rw [sub_mul, one_mul, htID] at hgrow
  have halving : ∀ q d : ℝ, q - (q - d) / 2 ≤ d → q ≤ d := by
    intro q d hd
    linarith only [hd]
  exact (not_le_of_gt hgd) (halving g d hgrow)

/-- An objective-error guarantee certifies the next localization radius. -/
theorem radius_of_objective_error {S : Set E} {F : E → ℝ} {μ R : ℝ} {xstar x : E}
    (hμ : 0 < μ) (hR : 0 ≤ R) (hF : StrongConvexOn S μ F)
    (hstar : xstar ∈ S) (hx : x ∈ S) (hmin : ∀ y ∈ S, F xstar ≤ F y)
    (herr : F x - F xstar ≤ μ / 2 * R ^ 2) : ‖x - xstar‖ ≤ R := by
  have h := (strongConvex_minimum_growth hμ.le hF hstar hx hmin).trans herr
  have hs : ‖x - xstar‖ ^ 2 ≤ R ^ 2 :=
    (mul_le_mul_left (by positivity : 0 < μ / 2)).mp h
  nlinarith [norm_nonneg (x - xstar)]

def envelopeInverse (μ D ε : ℝ) : ℝ :=
  if μ = 0 then ε / D else
    if ε ≤ μ * D ^ 2 / 2 then Real.sqrt (2 * μ * ε) else ε / D + μ * D / 2

theorem envelope_inverse_zero {D ε : ℝ} (hD : 0 < D) :
    envelope 0 D (envelopeInverse 0 D ε) = ε := by
  simp only [envelopeInverse, if_pos rfl, envelope_zero_curvature]
  exact mul_div_cancel₀ ε hD.ne'

theorem envelope_inverse_quadratic {μ D ε : ℝ} (hμ : 0 < μ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε) (hbranch : ε ≤ μ * D ^ 2 / 2) :
    envelope μ D (Real.sqrt (2 * μ * ε)) = ε := by
  have hsmall : Real.sqrt (2 * μ * ε) ≤ μ * D := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hbranch hμ.le]
  rw [envelope_quadratic hμ hsmall, Real.sq_sqrt (by positivity)]
  field_simp

theorem envelope_inverse_linear {μ D ε : ℝ} (hμ : 0 < μ)
    (hD : 0 < D) (hbranch : μ * D ^ 2 / 2 ≤ ε) :
    envelope μ D (ε / D + μ * D / 2) = ε := by
  have hlarge : μ * D ≤ ε / D + μ * D / 2 := by
    have he : μ * D ^ 2 / 2 / D ≤ ε / D := div_le_div_of_nonneg_right hbranch hD.le
    have heq : μ * D ^ 2 / 2 / D = μ * D / 2 := by field_simp; ring
    rw [heq] at he
    linarith
  rw [envelope_linear hμ hlarge]
  field_simp
  ring

theorem envelope_right_inverse {μ D ε : ℝ} (hμ : 0 ≤ μ)
    (hD : 0 < D) (hε : 0 ≤ ε) : envelope μ D (envelopeInverse μ D ε) = ε := by
  by_cases hz : μ = 0
  · subst μ
    exact envelope_inverse_zero hD
  have hp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
  unfold envelopeInverse
  rw [if_neg hz]
  split_ifs with hb
  · exact envelope_inverse_quadratic hp hD.le hε hb
  · exact envelope_inverse_linear hp hD (le_of_not_ge hb)

theorem envelope_pos {μ D a : ℝ} (hμ : 0 ≤ μ) (hD : 0 < D) (ha : 0 < a) :
    0 < envelope μ D a := by
  by_cases hz : μ = 0
  · simpa [hz, envelope_zero_curvature] using mul_pos hD ha
  have hp : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hz)
  have hm : 0 < (1 / 2 : ℝ) * min (D * a) (a ^ 2 / μ) := by positivity
  exact hm.trans_le (envelope_lower_min hp hD.le ha.le)

theorem envelope_strictMonoOn {μ D : ℝ} (hμ : 0 ≤ μ) (hD : 0 < D) :
    StrictMonoOn (envelope μ D) (Set.Ici 0) := by
  intro a ha b hb hab
  by_cases haz : a = 0
  · subst a
    have hzero : envelope μ D 0 = 0 := by
      exact le_antisymm (by simpa using envelope_le_linear (D := D) hμ (le_refl 0))
        (envelope_nonneg hμ hD.le (le_refl 0))
    rw [hzero]
    exact envelope_pos hμ hD hab
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hr : 0 < envelopeRadius μ D a := by
    unfold envelopeRadius
    split_ifs with hz
    · exact hD
    · exact lt_min hD (div_pos hap (lt_of_le_of_ne hμ (Ne.symm hz)))
  have hinc : envelope μ D a < radialObjective μ b (envelopeRadius μ D a) := by
    unfold envelope radialObjective
    nlinarith only [mul_pos (sub_pos.mpr hab) hr]
  exact hinc.trans_le (radialObjective_le_envelope hμ hb envelopeRadius_le)

theorem envelopeInverse_nonneg {μ D ε : ℝ} (hμ : 0 ≤ μ)
    (hD : 0 < D) (hε : 0 ≤ ε) : 0 ≤ envelopeInverse μ D ε := by
  unfold envelopeInverse
  split_ifs <;> positivity

theorem envelope_inverse_order {μ D ε a : ℝ} (hμ : 0 ≤ μ)
    (hD : 0 < D) (hε : 0 ≤ ε) (ha : 0 ≤ a) :
    envelope μ D a ≤ ε ↔ a ≤ envelopeInverse μ D ε := by
  simpa only [envelope_right_inverse hμ hD hε] using
    (envelope_strictMonoOn hμ hD).le_iff_le ha (envelopeInverse_nonneg hμ hD hε)

end
end HeavyTail
