import RandomizedFO2003.CascadeRadius

namespace RandomizedFO2003.Cascade

open Primitives Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Applying a self-adjoint left inverse to the actual three-term gradient
gives both normalized projection equations used in the activation argument. -/
theorem projected_gradient_equations (A L : E →L[ℝ] E) (hL : IsSelfAdjoint L)
    (hLA : ∀ y, L (A y) = y) (a b x g : E) (c t out χ' : ℝ)
    {α D : ℝ} (hα : α ≠ 0) (hD : D ≠ 0)
    (hg : g = A x - (c * t) • b - (out * χ' / α) • a) :
    (inner (𝕜 := ℝ) a (L g) / α = inner (𝕜 := ℝ) a x / α -
      c * (inner (𝕜 := ℝ) a (L b) / α) * t -
      (D * inner (𝕜 := ℝ) a (L a) / α ^ 2) * (out / D * χ')) ∧
    (inner (𝕜 := ℝ) b (L g) / D = inner (𝕜 := ℝ) b x / D -
      c * (inner (𝕜 := ℝ) b (L b) / D) * t -
      (inner (𝕜 := ℝ) a (L b) / α) * (out / D * χ')) := by
  have hLg : L g = x - (c * t) • L b - (out * χ' / α) • L a := by
    rw [hg, map_sub, map_sub, map_smul, map_smul, hLA]
  have hsym : inner (𝕜 := ℝ) b (L a) = inner (𝕜 := ℝ) a (L b) := by
    rw [← L.adjoint_inner_left a b, hL.adjoint_eq, real_inner_comm (L b) a]
  constructor
  · rw [hLg]
    simp only [inner_sub_right, inner_smul_right]
    field_simp
    ring
  · rw [hLg]
    simp only [inner_sub_right, inner_smul_right, hsym]
    field_simp
    ring

omit [CompleteSpace E] in
theorem normalized_projection_norm_bound (a : E) (L : E →L[ℝ] E) (g : E)
    {α : ℝ} (hα : 0 < α) :
    |inner (𝕜 := ℝ) a (L g) / α| ≤ (‖a‖ * ‖L‖ * ‖g‖) / α := by
  rw [abs_div, abs_of_pos hα]
  apply div_le_div_of_nonneg_right _ hα.le
  calc
    _ ≤ ‖a‖ * ‖L g‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a‖ * (‖L‖ * ‖g‖) := mul_le_mul_of_nonneg_left (L.le_opNorm g) (norm_nonneg a)
    _ = ‖a‖ * ‖L‖ * ‖g‖ := by ring

variable {N : ℕ}

theorem Data.projected_gradient_equations (d : Data N E)
    (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : d.D ≠ 0) (hα : d.α ≠ 0) (hB : 0 < d.B)
    (L : Fin (N + 1) → E →L[ℝ] E) (hL : ∀ i, IsSelfAdjoint (L i))
    (hLA : ∀ i x, L i (d.A i x) = x) (z : BlockProduct (N + 1) E)
    (i : Fin (N + 1)) (hz : ‖z i‖ ≤ d.B) :
    let v := inner (𝕜 := ℝ) (d.a i) (z i) / d.α
    let q := forcingReadout (d.b i) d.D (z i)
    let s := inner (𝕜 := ℝ) (d.a i) (L i (d.b i)) / d.α
    let k := d.D * inner (𝕜 := ℝ) (d.a i) (L i (d.a i)) / d.α ^ 2
    let r := inner (𝕜 := ℝ) (d.b i) (L i (d.b i)) / d.D
    let w := d.outgoing z i / d.D * deriv Primitives.gate v
    (inner (𝕜 := ℝ) (d.a i) (L i (gradient d.energy z i)) / d.α =
      v - d.incoming z i * s * saturationSlope d.K q - k * w) ∧
    (inner (𝕜 := ℝ) (d.b i) (L i (gradient d.energy z i)) / d.D =
      q - d.incoming z i * r * saturationSlope d.K q - s * w) := by
  exact RandomizedFO2003.Cascade.projected_gradient_equations (d.A i) (L i) (hL i) (hLA i) (d.a i) (d.b i) (z i)
    (gradient d.energy z i) (d.incoming z i) (saturationSlope d.K (forcingReadout (d.b i) d.D (z i)))
    (d.outgoing z i) (deriv Primitives.gate (inner (𝕜 := ℝ) (d.a i) (z i) / d.α)) hα hD
    (d.energy_gradient_identity_region hA hD hB z i hz)

/-- Smallness of the global gradient controls each normalized projection;
there is no additional assumption about the coordinate gradient. -/
theorem Data.gradient_projection_norm_bound (d : Data N E) (z : BlockProduct (N + 1) E)
    (i : Fin (N + 1)) (a : E) (L : E →L[ℝ] E) {α : ℝ} (hα : 0 < α) :
    |inner (𝕜 := ℝ) a (L (gradient d.energy z i)) / α| ≤
      (‖a‖ * ‖L‖ * ‖gradient d.energy z‖) / α := by
  apply (normalized_projection_norm_bound a L _ hα).trans
  apply div_le_div_of_nonneg_right _ hα.le
  exact mul_le_mul_of_nonneg_left (block_norm_le _ _) (mul_nonneg (norm_nonneg a) (norm_nonneg L))

end RandomizedFO2003.Cascade
