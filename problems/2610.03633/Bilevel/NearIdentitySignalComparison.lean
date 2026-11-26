import Bilevel.NearIdentityRestricted

/-! Comparison of actual restricted homotopies for two potentials.
Only their gradient difference is small; their individual gradients need
not be small relative to any hidden width. -/
noncomputable section
namespace Bilevel.NearIdentityInverse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem inverse_residual_bound {δ : NNReal} (hδ : δ<1) {G : E → E}
    (hG : LipschitzWith δ G) (u z : E) (t : Time) (B : ℝ)
    (hb : ‖z+(t:ℝ) • G z-u‖≤B) : ‖inverse hδ hG u t-z‖≤B/(1-(δ:ℝ)) := by
  have hh := (iteration_contracting hδ hG u t).dist_le_of_fixedPoint z
    (iteration_contracting hδ hG u t).fixedPoint_isFixedPt
  have he : z-iteration G u t z=z+(t:ℝ) • G z-u := by dsimp [iteration];abel
  rw [dist_eq_norm,dist_eq_norm,he,norm_sub_rev] at hh
  exact hh.trans (div_le_div_of_nonneg_right hb (by exact sub_nonneg.mpr hδ.le))

omit [CompleteSpace E] in
theorem restricted_ambient_equation (W : Submodule ℝ E) [CompleteSpace W]
    {δ : NNReal} (hδ : δ<1) {G : E → E} (hG : LipschitzWith δ G) (u : W) (t : Time)
    (hm : G (restrictedInverse W hδ hG u t)∈W) :
    (restrictedInverse W hδ hG u t:E)+(t:ℝ) • G (restrictedInverse W hδ hG u t)=(u:E) := by
  have hh := congrArg (fun z : W => (z:E)) (restrictedInverse_equation W hδ hG u t)
  have hp : (W.orthogonalProjection (G (restrictedInverse W hδ hG u t)):E)=
      G (restrictedInverse W hδ hG u t) := by
    exact congrArg (fun z : W => (z:E)) (W.orthogonalProjection_mem_subspace_eq_self ⟨_,hm⟩)
  simpa only [Submodule.coe_add,Submodule.coe_smul,hp] using hh

omit [CompleteSpace E] in
theorem restricted_compare_point (W : Submodule ℝ E) [CompleteSpace W]
    {δ : NNReal} (hδ : δ<1) {G H : E → E} (hG : LipschitzWith δ G)
    (u p : W) (t : Time) (B : ℝ) (heq : (p:E)+(t:ℝ) • H p=(u:E))
    (hb : ‖G p-H p‖≤B) :
    ‖(restrictedInverse W hδ hG u t:E)-(p:E)‖≤B/(1-(δ:ℝ)) := by
  apply inverse_residual_bound hδ (restrictedGradient_lipschitz W hG) u p t B
  have he : p+(t:ℝ) • restrictedGradient W G p-u=(t:ℝ) • W.orthogonalProjection (G p-H p) := by
    have hh := congrArg W.orthogonalProjection heq
    simp only [map_add,map_smul,W.orthogonalProjection_mem_subspace_eq_self] at hh
    rw [← hh]
    simp only [restrictedGradient,map_sub,smul_sub]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1]
  apply (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans
  exact (NearIdentityConfinement.projection_norm_le W (G p-H p)).trans hb

end Bilevel.NearIdentityInverse
