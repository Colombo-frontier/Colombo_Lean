import Bilevel.NearIdentityMinimizer
import Bilevel.NearIdentityConfinement

/-! Restriction to an actual closed linear subspace, with the query represented
as a member of that subspace. Existence, uniqueness, and continuity are derived.
Equality with the full inverse is conditional on the actual gradient support;
that construction-specific support is not assumed globally or concealed. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.NearIdentityInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def restrictedGradient (W : Submodule ℝ E) [CompleteSpace W] (G : E → E) (z : W) : W :=
  W.orthogonalProjection (G z)

omit [CompleteSpace E] in
theorem restrictedGradient_lipschitz (W : Submodule ℝ E) [CompleteSpace W]
    {δ : NNReal} {G : E → E} (hG : LipschitzWith δ G) :
    LipschitzWith δ (restrictedGradient W G) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, restrictedGradient, ← map_sub]
  exact (NearIdentityConfinement.projection_norm_le W (G x-G y)).trans
    (by simpa only [dist_eq_norm] using hG.dist_le_mul (x:E) (y:E))

theorem restricted_hasGradient (W : Submodule ℝ E) [CompleteSpace W]
    {P : E → ℝ} {G : E → E} (hP : ∀ z, HasGradientAt P (G z) z) (z : W) :
    HasGradientAt (fun w : W => P w) (restrictedGradient W G z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have h := (hP z).hasFDerivAt.comp z W.subtypeL.hasFDerivAt
  convert h using 1
  ext v
  simp only [InnerProductSpace.toDual_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, restrictedGradient,
    W.inner_orthogonalProjection_eq_of_mem_right]

def restrictedInverse (W : Submodule ℝ E) [CompleteSpace W] {δ : NNReal}
    (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G) (u : W) (t : Time) : W :=
  inverse hδ (restrictedGradient_lipschitz W hG) u t

def restrictedPath (W : Submodule ℝ E) [CompleteSpace W] {δ : NNReal}
    (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G) (u : W) (t : Time) : E :=
  restrictedInverse W hδ hG u t

omit [CompleteSpace E] in
theorem restrictedPath_zero (W : Submodule ℝ E) [CompleteSpace W] {δ : NNReal}
    (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G) (u : W) :
    restrictedPath W hδ hG u ⟨0,by constructor <;> norm_num⟩=(u:E) := by
  exact congrArg (fun z : W => (z:E))
    (inverse_zero hδ (restrictedGradient_lipschitz W hG) u)

omit [CompleteSpace E] in
theorem restrictedInverse_equation (W : Submodule ℝ E) [CompleteSpace W] {δ : NNReal}
    (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G) (u : W) (t : Time) :
    restrictedInverse W hδ hG u t + (t:ℝ) •
      W.orthogonalProjection (G (restrictedInverse W hδ hG u t)) = u :=
  inverse_equation hδ (restrictedGradient_lipschitz W hG) u t

omit [CompleteSpace E] in
theorem restrictedInverse_continuous (W : Submodule ℝ E) [CompleteSpace W] {δ : NNReal}
    (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G) (u : W) :
    Continuous (fun t : Time => (restrictedInverse W hδ hG u t : E)) :=
  continuous_subtype_val.comp (inverse_continuous hδ (restrictedGradient_lipschitz W hG) u)

theorem restrictedInverse_unique_minimizer (W : Submodule ℝ E) [CompleteSpace W]
    {δ : NNReal} (hδ : δ < 1) {G : E → E} (P : E → ℝ)
    (hP : ∀ z, HasGradientAt P (G z) z) (hG : LipschitzWith δ G)
    (u y : W) (t : Time) :
    (∀ z : W, objective P (u:E) t (y:E) ≤ objective P (u:E) t (z:E)) ↔
      y=restrictedInverse W hδ hG u t := by
  exact inverse_unique_minimizer hδ (fun z : W => P z)
    (restricted_hasGradient W hP) (restrictedGradient_lipschitz W hG) u y t

/-- Once actual support has been proved at the restricted minimizer, it is the
unrestricted inverse. This does not assume any oracle transcript coupling. -/
theorem restrictedInverse_eq_full_of_gradient_mem (W : Submodule ℝ E) [CompleteSpace W]
    {δ : NNReal} (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G)
    (u : W) (t : Time)
    (hsupport : G (restrictedInverse W hδ hG u t) ∈ W) :
    (restrictedInverse W hδ hG u t : E) = inverse hδ hG (u:E) t := by
  apply inverse_unique hδ hG (u:E) _ t
  have h := congrArg (fun z : W => (z:E)) (restrictedInverse_equation W hδ hG u t)
  have hp : (W.orthogonalProjection (G (restrictedInverse W hδ hG u t)) : E) =
      G (restrictedInverse W hδ hG u t) := by
    exact congrArg (fun z : W => (z:E))
      (W.orthogonalProjection_mem_subspace_eq_self ⟨_,hsupport⟩)
  simpa only [Submodule.coe_add, Submodule.coe_smul, hp] using h

end Bilevel.NearIdentityInverse
