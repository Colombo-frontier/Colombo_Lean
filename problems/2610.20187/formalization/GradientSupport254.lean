import SurrogateDomination254

noncomputable section
open scoped RealInnerProductSpace
namespace Paper254

/-- First-order convex support follows from exp-concavity itself; convexity
is not added as an independent assumption to the problem definition. -/
theorem gradient_support {d : ℕ} {D η : ℝ} (W : Domain d D)
    (hη : 0 < η) {f : Loss d} (hf : ExpConcaveOn η W.carrier f)
    {g w v : Space d} (hd : HasGradientWithinAt f g W.carrier w)
    (hw : w ∈ W.carrier) (hv : v ∈ W.carrier) :
    ⟪g,v-w⟫ ≤ f v-f w := by
  have hs := concave_support hf hw hv ((hd.hasFDerivWithinAt.const_mul (-η)).exp)
  simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply,
    smul_eq_mul] at hs
  have he : Real.exp (-η*f w)*Real.exp (-η*(f v-f w)) = Real.exp (-η*f v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp (-η*(f v-f w)) ≤ 1-η*⟪g,v-w⟫ := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (-η*f w))).mp
    rw [he]
    nlinarith [hs]
  have hlo := Real.add_one_le_exp (-η*(f v-f w))
  have hprod : η*⟪g,v-w⟫ ≤ η*(f v-f w) := by linarith
  exact (mul_le_mul_iff_right₀ hη).mp hprod

def selectedGradient {d : ℕ} {D : ℝ} (W : Domain d D) (G : ℝ)
    (f : Loss d) (w : W.carrier) : Space d := by
  classical
  exact if h : ∃ g : Space d, HasGradientWithinAt f g W.carrier w.val ∧ ‖g‖ ≤ G
    then h.choose else 0

theorem selectedGradient_spec {d : ℕ} {D G η : ℝ} (W : Domain d D)
    {f : Loss d} (hf : AdmissibleLoss W G η f) (w : W.carrier) :
    HasGradientWithinAt f (selectedGradient W G f w) W.carrier w.val ∧
      ‖selectedGradient W G f w‖ ≤ G := by
  classical
  have h := hf.gradient w.val w.property
  simp only [selectedGradient, dif_pos h]
  exact h.choose_spec

end Paper254
#print axioms Paper254.gradient_support
#print axioms Paper254.selectedGradient_spec
