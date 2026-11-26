import NCConcave16991.GlobalHardConnectorLocalGradient

/-! # Actual affine two-port derivatives, including the public cap -/

namespace NCConcave16991.GlobalHard
noncomputable section
open LocalizationScalar LocalizationRadial LocalizationHessian
open scoped InnerProductSpace

variable {A E : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem affine_direction_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a h : F) :
    HasDerivAt (fun t : ℝ ↦ a + (t - 1) • h) h 1 := by
  convert ((((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const h).const_add a) using 1 <;> simp

theorem radialCap_affine_hasDerivAt {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {C : ℝ} (hC : 0 < C) (a h : F) :
    HasDerivAt (fun t : ℝ ↦ radialCap C (a + (t - 1) • h)) (fderiv ℝ (radialCap C) a h) 1 := by
  have hc : HasFDerivAt (radialCap C) (fderiv ℝ (radialCap C) a) (a + ((1 : ℝ) - 1) • h) := by
    simpa using (radialCap_differentiable hC a).hasFDerivAt
  convert hc.comp_hasDerivAt 1 (affine_direction_hasDerivAt a h) using 1 <;> rfl

def portOuterDerivative (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E) (ha : A) (hb : E) : ℝ :=
  -4 * activationLoad previous (stateScore v s) * ⟪u, fderiv ℝ (radialCap 21) a ha⟫_ℝ -
    activationLoad previous (stateScore v s) * ⟪radialCap 10 s, fderiv ℝ (radialCap 21) b hb⟫_ℝ

theorem outerStage_port_hasDerivAt (u : A) (v : E) (previous : ℝ) (s : E) (a : A) (b : E) (ha : A) (hb : E) :
    HasDerivAt (fun t : ℝ ↦ outerStage u v previous s (a + (t - 1) • ha) (b + (t - 1) • hb))
      (portOuterDerivative u v previous s a b ha hb) 1 := by
  have hA := (innerSL ℝ u).hasFDerivAt.comp_hasDerivAt 1
    (radialCap_affine_hasDerivAt (by norm_num : (0 : ℝ) < 21) a ha)
  have hB := (innerSL ℝ (radialCap 10 s)).hasFDerivAt.comp_hasDerivAt 1
    (radialCap_affine_hasDerivAt (by norm_num : (0 : ℝ) < 21) b hb)
  have hh := (((hasDerivAt_const (1 : ℝ) (statePenalty v s)).add
    (hA.const_mul (-4 * activationLoad previous (stateScore v s)))).sub
    (hB.const_mul (activationLoad previous (stateScore v s)))).add_const
      (stateCoupling previous (stateScore v s))
  convert hh using 1
  · funext t
    simp only [outerStage, entrance, exit, innerSL_apply_apply, Function.comp_apply, Pi.add_apply, Pi.sub_apply]
    ring
  · simp only [portOuterDerivative, innerSL_apply_apply]
    ring

def portObjective (u : A) (v : E) (previous : ℝ) (s : E) (d r : ℝ) (root : A) (terminal : E)
    (c : ℝ) (a : A) (b : E) : ℝ :=
  d * (‖a‖ ^ 2 + ‖b‖ ^ 2) + r * (⟪a, root⟫_ℝ - ⟪b, terminal⟫_ℝ) + c +
    outerStage u v previous s a b

def portDerivative (u : A) (v : E) (previous : ℝ) (s : E) (d r : ℝ) (root : A) (terminal : E)
    (a : A) (b : E) (ha : A) (hb : E) : ℝ :=
  2 * d * (⟪a, ha⟫_ℝ + ⟪b, hb⟫_ℝ) + r * (⟪ha, root⟫_ℝ - ⟪hb, terminal⟫_ℝ) +
    portOuterDerivative u v previous s a b ha hb

theorem portObjective_hasDerivAt (u : A) (v : E) (previous : ℝ) (s : E) (d r : ℝ) (root : A) (terminal : E)
    (c : ℝ) (a : A) (b : E) (ha : A) (hb : E) :
    HasDerivAt (fun t : ℝ ↦ portObjective u v previous s d r root terminal c
      (a + (t - 1) • ha) (b + (t - 1) • hb))
      (portDerivative u v previous s d r root terminal a b ha hb) 1 := by
  have hA := affine_direction_hasDerivAt a ha
  have hB := affine_direction_hasDerivAt b hb
  have hqa := hA.norm_sq
  have hqb := hB.norm_sq
  have hia := hA.inner ℝ (hasDerivAt_const (1 : ℝ) root)
  have hib := hB.inner ℝ (hasDerivAt_const (1 : ℝ) terminal)
  have hh := ((((hqa.add hqb).const_mul d).add ((hia.sub hib).const_mul r)).add_const c).add
    (outerStage_port_hasDerivAt u v previous s a b ha hb)
  convert hh using 1
  · funext t
    simp only [portObjective, Pi.add_apply, Pi.sub_apply]
  · simp only [portDerivative, sub_self, zero_smul, add_zero, inner_zero_right, zero_add]
    ring

end
end NCConcave16991.GlobalHard
