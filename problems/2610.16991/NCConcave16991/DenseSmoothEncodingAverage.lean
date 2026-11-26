/- Adapted from the proved radial-calculus fragments in ../0105_formalization/Manuscript0105/EncodingAverage.lean. No assumed lower bounds are imported. -/
import NCConcave16991.DenseSmoothRadialBasics

/-!
# Fixed-table encoding average

This file proves equation `(average-q)`: a table whose row average is `ρu` has scaled radial
coordinates whose component average is exactly the hidden radial coordinate in direction `u`.
-/

open scoped BigOperators InnerProductSpace

namespace NCConcave16991.DenseSmooth

section

variable {n : ℕ} [NeZero n]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def scaledRadialCoordinate (ρ : ℝ) (s x : E) : ℝ :=
  ρ⁻¹ * radialCoordinate s x

theorem average_scaledRadialCoordinate
    {ρ : ℝ} (hρ : ρ ≠ 0) (rows : Fin n → E) (u x : E)
    (hrows : ∑ i, rows i = ((n : ℝ) * ρ) • u) :
    (∑ i, scaledRadialCoordinate ρ (rows i) x) / n = radialCoordinate u x := by
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_ne_zero (NeZero.ne n)))
  have hden : Real.sqrt (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
  rw [radialCoordinate]
  dsimp [scaledRadialCoordinate, radialCoordinate]
  rw [← Finset.mul_sum]
  have hsumInner : ∑ i, ⟪rows i, x⟫_ℝ = (n : ℝ) * ρ * ⟪u, x⟫_ℝ := by
    calc
      ∑ i, ⟪rows i, x⟫_ℝ = ⟪∑ i, rows i, x⟫_ℝ := by
        simpa using (sum_inner (𝕜 := ℝ) Finset.univ rows x).symm
      _ = ⟪((n : ℝ) * ρ) • u, x⟫_ℝ := by rw [hrows]
      _ = (n : ℝ) * ρ * ⟪u, x⟫_ℝ := by rw [real_inner_smul_left]
  rw [← Finset.sum_div]
  rw [hsumInner]
  field_simp

end

end NCConcave16991.DenseSmooth
