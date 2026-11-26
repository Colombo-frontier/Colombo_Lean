import Mathlib

/-!
Convex first-order inequalities and normal-certificate gap bounds. The generic
certificate theorem takes the scalar saddle first-order inequality explicitly;
it does not assert the full manuscript class has been instantiated.
-/
open Set Metric
open scoped Topology
namespace MinimaxAudit

section FirstOrder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convex_first_order {s : Set E} {f : E → ℝ} {x y : E}
    {df : E →L[ℝ] ℝ} (hc : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s)
    (hd : HasFDerivAt f df x) : df (y - x) ≤ f y - f x := by
  have hdline : HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)) (df (y - x)) (0 : ℝ) := by
    apply HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) _
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y))
    simpa using hd
  have h := (hc.comp_affineMap (AffineMap.lineMap x y)).le_slope_of_hasDerivAt
    (x := (0 : ℝ)) (y := (1 : ℝ)) (by simpa using hx) (by simpa using hy)
    (by norm_num) hdline
  simpa [slope] using h

end FirstOrder

section Certificates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Outward normal cone, matching equation `normal-definition`. -/
def normalCone (Z : Set E) (z : E) : Set E :=
  {v | ∀ z' ∈ Z, inner ℝ v (z' - z) ≤ 0}

/-- A scalar comparison value controlled by any feasible normal certificate. -/
theorem comparison_le_normal_certificate {Z : Set E} {z z' F v : E} {D g : ℝ}
    (hz' : z' ∈ Z) (hv : v ∈ normalCone Z z)
    (hD : ‖z - z'‖ ≤ D) (hg : g ≤ inner ℝ F (z - z')) :
    g ≤ D * ‖F + v‖ := by
  have hn : 0 ≤ inner ℝ v (z - z') := by
    have := hv z' hz'
    rw [show z - z' = -(z' - z) by abel, inner_neg_right]
    linarith
  calc
    g ≤ inner ℝ (F + v) (z - z') := by rw [inner_add_left]; linarith
    _ ≤ ‖F + v‖ * ‖z - z'‖ := real_inner_le_norm _ _
    _ ≤ ‖F + v‖ * D := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = D * ‖F + v‖ := mul_comm _ _

/-- The supremum step in `lem:criteria`, with all witnesses quantified. -/
theorem comparison_sup_le_normal_certificate {Z : Set E} {z F v : E} {D : ℝ}
    {g : E → ℝ} (hne : Z.Nonempty) (hv : v ∈ normalCone Z z)
    (hD : ∀ z' ∈ Z, ‖z - z'‖ ≤ D)
    (hg : ∀ z' ∈ Z, g z' ≤ inner ℝ F (z - z')) :
    sSup (g '' Z) ≤ D * ‖F + v‖ := by
  apply csSup_le (hne.image g)
  rintro _ ⟨z', hz', rfl⟩
  exact comparison_le_normal_certificate hz' hv (hD z' hz') (hg z' hz')

end Certificates
end MinimaxAudit
