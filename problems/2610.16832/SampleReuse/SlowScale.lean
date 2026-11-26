import SecondOrder.ScaledFirstOrderGeometry
import SecondOrder.ScaledFirstOrderCompletion

/-! The slow coordinate scale in the supplied manuscript. The predecessor
uses sqrt(d) inside tanh; dilation by 1 / d^(1/4) gives exactly the new scale.
Its T+1 blocks correspond to the manuscript's T blocks by reindexing. -/

open SecondOrder
open scoped BigOperators

namespace SampleReuse
noncomputable section

def slowAlpha (d : ℕ) : ℝ := Real.sqrt (Real.sqrt d)
def slowDilation (d : ℕ) : ℝ := (slowAlpha d)⁻¹

theorem slowAlpha_pos {d : ℕ} (hd : 0 < d) : 0 < slowAlpha d := by
  exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))

theorem slowAlpha_sq (d : ℕ) : slowAlpha d ^ 2 = Real.sqrt d :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem slowAlpha_fourth (d : ℕ) : slowAlpha d ^ 4 = d := by
  calc
    _ = (slowAlpha d ^ 2)^2 := by ring
    _ = (Real.sqrt d)^2 := by rw [slowAlpha_sq]
    _ = d := Real.sq_sqrt (Nat.cast_nonneg _)

theorem slowAlpha_rpow (d : ℕ) : slowAlpha d = (d : ℝ)^(1/4:ℝ) := by
  unfold slowAlpha
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg d)]
  norm_num

theorem slowDilation_scale {d : ℕ} (hd : 0 < d) :
    Real.sqrt d * slowDilation d = slowAlpha d := by
  rw [← slowAlpha_sq]
  unfold slowDilation
  field_simp [ne_of_gt (slowAlpha_pos hd)]
  ring

def slowEncoding {d : ℕ} (θ : Fin d → Bool) (x : Point d) : ℝ :=
  ∑ i, (2/(d:ℝ))*signValue (θ i)*Real.tanh (slowAlpha d*x i)

/-- Exact equality of the scalar encodings, hence not merely a rate analogy. -/
theorem slowEncoding_eq {d : ℕ} (hd : 0 < d) (θ : Fin d → Bool) (x : Point d) :
    firstOrderBlockEncoding θ (slowDilation d • x) = slowEncoding θ x := by
  unfold firstOrderBlockEncoding firstOrderCoefficientEncoding separablePotential slowEncoding
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, slowDilation_scale hd]

theorem slowDilation_sq (d : ℕ) :
    slowDilation d ^ 2 = (Real.sqrt d)⁻¹ := by
  rw [slowDilation, inv_pow, slowAlpha_sq]

theorem slowDilation_cubic {d : ℕ} (hd : 0 < d) :
    slowDilation d ^ 3 * Real.sqrt d = slowDilation d := by
  rw [← slowAlpha_sq]
  unfold slowDilation
  field_simp [ne_of_gt (slowAlpha_pos hd)]
  ring

/-- Genuine population Hessian and third-derivative bounds at the slow scale.
The third derivative bound for the sampled noise remains a separate obligation. -/
theorem slow_population_derivative_bounds {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (x : Point (FirstOrderDimension d T)) :
    ‖hessian (scaledFirstOrderPopulation Θ A (slowDilation d)) x‖ ≤
      A*(Real.sqrt d)⁻¹*firstOrderGeometryConstant ∧
    ‖iteratedFDeriv ℝ 3 (scaledFirstOrderPopulation Θ A (slowDilation d)) x‖ ≤
      A*slowDilation d*firstOrderGeometryConstant := by
  have hb := scaledFirstOrderPopulation_derivative_bounds Θ hd hA
    (show 0 ≤ slowDilation d from inv_nonneg.mpr (slowAlpha_pos hd).le) x
  constructor
  · simpa only [slowDilation_sq d] using hb.1
  · calc
      _ ≤ A*slowDilation d^3*(firstOrderGeometryConstant*Real.sqrt d) := hb.2
      _ = A*(slowDilation d^3*Real.sqrt d)*firstOrderGeometryConstant := by ring
      _ = _ := by rw [slowDilation_cubic hd]

/-- The stationarity obstruction for the actual slow-coordinate scalar loss. -/
theorem slow_stationarity_obstruction {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (x : Point (FirstOrderDimension d T))
    (hu : ∃ j, slowEncoding (Θ j) ((firstOrderCoordinates d T x) j) ≤ 1/2) :
    A*slowDilation d*firstOrderGradientConstant ≤
      ‖gradient (scaledFirstOrderPopulation Θ A (slowDilation d)) x‖ := by
  apply scaledFirstOrderPopulation_gradient_lower Θ hd hA
    (inv_nonneg.mpr (slowAlpha_pos hd).le) x
  obtain ⟨j, hj⟩ := hu
  refine ⟨j, ?_⟩
  change firstOrderBlockEncoding (Θ j)
    (slowDilation d • ((firstOrderCoordinates d T x) j)) ≤ 1/2
  rwa [slowEncoding_eq hd]

theorem slow_stationary_all_blocks {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) {A ε : ℝ} (hA : 0 ≤ A)
    (hε : ε < A*slowDilation d*firstOrderGradientConstant)
    (x : Point (FirstOrderDimension d T))
    (hx : ‖gradient (scaledFirstOrderPopulation Θ A (slowDilation d)) x‖ ≤ ε) :
    ∀ j, 1/2 < slowEncoding (Θ j) ((firstOrderCoordinates d T x) j) := by
  intro j
  by_contra hj
  have h := slow_stationarity_obstruction Θ hd hA x ⟨j, le_of_not_gt hj⟩
  exact (not_lt_of_ge (h.trans hx)) hε

end
end SampleReuse
