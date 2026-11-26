import Bilevel.ChiOuterActiveForce
import Bilevel.ChiOuterInactiveForce

/-! One fixed profile constant simultaneously bounds the actual active and
fixed inactive pre-wrapper source forces, before all geometric parameters. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiRecursive ChiCarrier SmallGapLiftSupport

private theorem force_bound_mono (P : ChiFine.Parameters) (lambdaExt : ℝ) (hlambda : 0≤lambdaExt)
    {A B : ℝ} (hAB : A≤B) :
    2*C*A*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ≤2*C*B*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ := by
  have hfactor : 0≤2*C*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ := by
    have := C_pos
    have := P.c_pos
    have := P.ell_nonneg
    positivity
  convert mul_le_mul_of_nonneg_right hAB hfactor using 1 <;> ring

theorem active_inactive_latent_force_bound : ∃ B : ℝ,1≤B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (m : ℕ) (M : Node E) (D : Geometry F) (P : ChiFine.Parameters) (lambdaExt : ℝ),0≤lambdaExt →
      ∀ (s : ℝ) (d : ℕ) (a : E) (x : Blocks m F),
      ‖outerFineLatentForce m M D P lambdaExt s d a x‖≤
        2*C*B*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ ∧
      ‖outerInactiveLatentForce m M D P lambdaExt s d a x‖≤
        2*C*B*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ := by
  obtain ⟨A,hA,ha⟩ := outerFineLatentForce_bound
  obtain ⟨B,hB,hb⟩ := outerInactiveLatentForce_bound
  refine ⟨A+B,by linarith,fun E F _ _ _ _ _ _ m M D P lambdaExt hlambda s d a x => ?_⟩
  constructor
  · exact (ha E F m M D P lambdaExt hlambda s d a x).trans
      (force_bound_mono P lambdaExt hlambda (by linarith : A≤A+B))
  · exact (hb E F m M D P lambdaExt hlambda s d a x).trans
      (force_bound_mono P lambdaExt hlambda (by linarith : B≤A+B))

end Bilevel.ChiOuter
