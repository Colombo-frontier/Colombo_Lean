import SecondOrder.GateProperties

namespace SecondOrder
noncomputable section

def affineGate (s a x : ℝ) : ℝ := gate (s*(x-a))
def affineGateFirst (s a x : ℝ) : ℝ := s*gateFirst (s*(x-a))
def affineGateSecond (s a x : ℝ) : ℝ := s^2*gateSecond (s*(x-a))
def affineGateThird (s a x : ℝ) : ℝ := s^3*gateThird (s*(x-a))

theorem affineGate_hasDerivAt (s a x : ℝ) :
    HasDerivAt (affineGate s a) (affineGateFirst s a x) x := by
  convert (gate_hasDerivAt (s*(x-a))).comp x (((hasDerivAt_id x).sub_const a).const_mul s) using 1 <;>
    simp only [affineGate, affineGateFirst, id_eq, mul_one] <;> ring

theorem affineGateFirst_hasDerivAt (s a x : ℝ) :
    HasDerivAt (affineGateFirst s a) (affineGateSecond s a x) x := by
  convert ((gateFirst_hasDerivAt (s*(x-a))).comp x
    (((hasDerivAt_id x).sub_const a).const_mul s)).const_mul s using 1 <;>
    simp only [affineGateFirst, affineGateSecond, id_eq, mul_one] <;> ring

theorem affineGateSecond_hasDerivAt (s a x : ℝ) :
    HasDerivAt (affineGateSecond s a) (affineGateThird s a x) x := by
  convert ((gateSecond_hasDerivAt (s*(x-a))).comp x
    (((hasDerivAt_id x).sub_const a).const_mul s)).const_mul (s^2) using 1 <;>
    simp only [affineGateSecond, affineGateThird, id_eq, mul_one] <;> ring

theorem deriv_affineGate (s a : ℝ) : deriv (affineGate s a) = affineGateFirst s a :=
  funext (fun x => (affineGate_hasDerivAt s a x).deriv)
theorem deriv_affineGateFirst (s a : ℝ) : deriv (affineGateFirst s a) = affineGateSecond s a :=
  funext (fun x => (affineGateFirst_hasDerivAt s a x).deriv)
theorem deriv_affineGateSecond (s a : ℝ) : deriv (affineGateSecond s a) = affineGateThird s a :=
  funext (fun x => (affineGateSecond_hasDerivAt s a x).deriv)

theorem affineGate_contDiff (s a : ℝ) : ContDiff ℝ 3 (affineGate s a) :=
  gate_contDiff_three.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem affineGate_fisher (s a x : ℝ) :
    (deriv (affineGate s a) x)^2 ≤ 1225*s^2*affineGate s a x*(1-affineGate s a x) := by
  have h := mul_le_mul_of_nonneg_left (gate_fisher (s*(x-a))) (sq_nonneg s)
  rw [deriv_gate] at h
  rw [deriv_affineGate]
  dsimp [affineGateFirst, affineGate]
  nlinarith [h]

theorem affineGate_flat_left {s a x : ℝ} (hs : 0 ≤ s) (hx : x ≤ a) :
    affineGate s a x = 0 ∧ affineGateFirst s a x = 0 ∧
      affineGateSecond s a x = 0 ∧ affineGateThird s a x = 0 := by
  have h := gate_flat_left (mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hx))
  simp only [affineGate, affineGateFirst, affineGateSecond, affineGateThird, h.1, h.2.1, h.2.2.1, h.2.2.2, mul_zero, and_self]

theorem affineGate_flat_right {s a x : ℝ} (hx : 1 ≤ s*(x-a)) :
    affineGate s a x = 1 ∧ affineGateFirst s a x = 0 ∧
      affineGateSecond s a x = 0 ∧ affineGateThird s a x = 0 := by
  have h := gate_flat_right hx
  simp only [affineGate, affineGateFirst, affineGateSecond, affineGateThird, h.1, h.2.1, h.2.2.1, h.2.2.2, mul_zero, and_self]

theorem affineGate_nonnegative_derivatives {s a x : ℝ} (hs : 0 ≤ s) (hx : s*(x-a) ≤ 1/2) :
    0 ≤ deriv (affineGate s a) x ∧ 0 ≤ deriv (deriv (affineGate s a)) x := by
  rw [deriv_affineGate, deriv_affineGateFirst]
  exact ⟨mul_nonneg hs (gateFirst_nonneg _), mul_nonneg (sq_nonneg s) (gateSecond_nonneg hx)⟩

/-- Scalar completion gates used by the curvature and first-order constructions. -/
def curvatureCompletion : ℝ → ℝ := affineGate (64/3) (1/128)
def firstOrderCompletion : ℝ → ℝ := affineGate 2 (1/4)

theorem curvatureCompletion_contDiff : ContDiff ℝ 3 curvatureCompletion := affineGate_contDiff _ _
theorem firstOrderCompletion_contDiff : ContDiff ℝ 3 firstOrderCompletion := affineGate_contDiff _ _

theorem curvatureCompletion_half : curvatureCompletion (1/32) = 1/2 := by
  change gate ((64/3)*(1/32-1/128)) = 1/2
  norm_num
  exact gate_half

theorem firstOrderCompletion_half : firstOrderCompletion (1/2) = 1/2 := by
  change gate (2*(1/2-1/4)) = 1/2
  norm_num
  exact gate_half

theorem curvatureCompletion_gt_half {x : ℝ} (hx : 1/32 < x) : 1/2 < curvatureCompletion x :=
  gate_gt_half (by linarith)

theorem firstOrderCompletion_gt_half {x : ℝ} (hx : 1/2 < x) : 1/2 < firstOrderCompletion x :=
  gate_gt_half (by linarith)

theorem curvatureCompletion_flat {x : ℝ} (hx : x ≤ 1/128) :
    curvatureCompletion x = 0 ∧ deriv curvatureCompletion x = 0 ∧
      deriv (deriv curvatureCompletion) x = 0 ∧ deriv (deriv (deriv curvatureCompletion)) x = 0 := by
  unfold curvatureCompletion
  rw [deriv_affineGate, deriv_affineGateFirst, deriv_affineGateSecond]
  exact affineGate_flat_left (by norm_num) hx

theorem firstOrderCompletion_flat {x : ℝ} (hx : x ≤ 1/4) :
    firstOrderCompletion x = 0 ∧ deriv firstOrderCompletion x = 0 ∧
      deriv (deriv firstOrderCompletion) x = 0 ∧ deriv (deriv (deriv firstOrderCompletion)) x = 0 := by
  unfold firstOrderCompletion
  rw [deriv_affineGate, deriv_affineGateFirst, deriv_affineGateSecond]
  exact affineGate_flat_left (by norm_num) hx

theorem curvatureCompletion_one {x : ℝ} (hx : 7/128 ≤ x) : curvatureCompletion x = 1 :=
  (affineGate_flat_right (by linarith : 1 ≤ (64/3)*(x-1/128))).1

theorem firstOrderCompletion_one {x : ℝ} (hx : 3/4 ≤ x) : firstOrderCompletion x = 1 :=
  (affineGate_flat_right (by linarith : 1 ≤ 2*(x-1/4))).1

theorem curvatureCompletion_derivatives_nonneg {x : ℝ} (hx : x ≤ 1/32) :
    0 ≤ deriv curvatureCompletion x ∧ 0 ≤ deriv (deriv curvatureCompletion) x :=
  affineGate_nonnegative_derivatives (by norm_num) (by linarith)

theorem firstOrderCompletion_derivatives_nonneg {x : ℝ} (hx : x ≤ 1/2) :
    0 ≤ deriv firstOrderCompletion x ∧ 0 ≤ deriv (deriv firstOrderCompletion) x :=
  affineGate_nonnegative_derivatives (by norm_num) (by linarith)

end
end SecondOrder
