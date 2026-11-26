import Smoothness2601.TruncatedGradients
import Smoothness2601.PrefixSimulator

/-! Frame-column truncation equals differentiation with constant zero latent
coordinates. Orthonormality is unnecessary for these identities. -/
noncomputable section
namespace Smoothness2601.FrameTruncation
open ExtensiveChain PrefixSimulator
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def synthesis {n : ℕ} (U : Fin (n+1) → E) : ExtensiveChain.Space n →L[ℝ] E :=
  ∑ i, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (U i)

def coordinates {n : ℕ} (U : Fin (n+1) → E) : E →L[ℝ] ExtensiveChain.Space n := (synthesis U).adjoint

omit [CompleteSpace E] in
theorem synthesis_apply {n : ℕ} (U : Fin (n+1) → E) (z : ExtensiveChain.Space n) :
    synthesis U z = ∑ i, z i • U i := by simp [synthesis]

omit [CompleteSpace E] in
theorem synthesis_single {n : ℕ} (U : Fin (n+1) → E) (i : Fin (n+1)) :
    synthesis U (EuclideanSpace.single i 1) = U i := by
  rw [synthesis_apply]
  simp [EuclideanSpace.single_apply]

theorem coordinates_apply {n : ℕ} (U : Fin (n+1) → E) (w : E) (i : Fin (n+1)) :
    coordinates U w i = ⟪U i,w⟫ := by
  have hi := ContinuousLinearMap.adjoint_inner_right (synthesis U) (EuclideanSpace.single i 1) w
  simpa [coordinates,synthesis_single,EuclideanSpace.inner_single_left] using hi

def clip {n : ℕ} (U : Fin (n+1) → E) (k : ℕ) : Fin (n+1) → E :=
  fun i => if i.val < k then U i else 0

theorem coordinates_clip {n : ℕ} (U : Fin (n+1) → E) (k : ℕ) :
    coordinates (clip U k) = (cutProjection k).comp (coordinates U) := by
  ext w i
  simp only [coordinates_apply,ContinuousLinearMap.comp_apply,cutProjection_apply,clip]
  split_ifs <;> simp

omit [CompleteSpace E] in
theorem synthesis_isometry {n : ℕ} (U : ExtensiveChain.Space n →ₗᵢ[ℝ] E) :
    synthesis (fun i => U (EuclideanSpace.single i 1)) = U.toContinuousLinearMap := by
  ext z
  rw [synthesis_apply]
  simp_rw [← U.map_smul]
  rw [← map_sum]
  have he : (∑ j, z j • EuclideanSpace.single j 1 : ExtensiveChain.Space n) = z := by
    ext i
    change (EuclideanSpace.proj (𝕜 := ℝ) i) (∑ j, z j • EuclideanSpace.single j 1) = _
    simp [map_sum,EuclideanSpace.single_apply]
  exact congrArg U he

def extensiveProfile (R M : ℝ) {n : ℕ} (U : Fin (n+1) → E) : E → ℝ :=
  RadialWrapper.wrapped R (1/16) (coordinates U) (extensive M)

def frontierProfile (R : ℝ) {n : ℕ} (U : Fin (n+1) → E) : E → ℝ :=
  RadialWrapper.carried R (coordinates U) Cutoffs.frontier

theorem gradient_add_eq {f g : E → ℝ} {w : E}
    (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    gradient (fun x => f x+g x) w = gradient f w+gradient g w := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hf.hasGradientAt.hasFDerivAt.add hg.hasGradientAt.hasFDerivAt using 1
  ext v
  simp [InnerProductSpace.toDual_apply,inner_add_left]

theorem extensive_profile_clip (R M : ℝ) {n : ℕ} (U : Fin (n+1) → E) (k : ℕ) (w : E)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |⟪U i,Bilevel.RadialWrapper.compress R w⟫| ≤ 1/16) :
    gradient (extensiveProfile R M (clip U k)) w = gradient (extensiveProfile R M U) w := by
  have he : RadialWrapper.carried R (coordinates (clip U k)) (extensive M) =
      RadialWrapper.carried R (coordinates U) (fun z => extensive M (cutProjection k z)) := by
    funext x
    simp only [RadialWrapper.carried,coordinates_clip,ContinuousLinearMap.comp_apply]
  have htail' : ∀ i : Fin (n+1), k ≤ i.val → |coordinates U (Bilevel.RadialWrapper.compress R w) i| ≤ 1/16 := by
    simpa only [coordinates_apply] using htail
  have hgrad := carried_extensive_truncated_gradient R M k (coordinates U) w htail'
  unfold extensiveProfile RadialWrapper.wrapped
  rw [he]
  have hc := (RadialWrapper.carried_contDiff R (coordinates U) (extensive M) 1
    ((extensive_contDiff M n).of_le (by norm_num))).differentiable (by norm_num) w
  have hct : DifferentiableAt ℝ
      (RadialWrapper.carried R (coordinates U) (fun z => extensive M (cutProjection k z))) w := by
    exact (RadialWrapper.carried_hasGradientAt R (coordinates U) _ _
      (fun z => cut_comp_hasGradientAt k (extensive_hasFDerivAt M (cutProjection k z)).differentiableAt.hasGradientAt) w).differentiableAt
  have hq := (RadialWrapper.quadratic_hasGradientAt (E := E) (1/16) w).differentiableAt
  rw [gradient_add_eq hct hq,gradient_add_eq hc hq,hgrad]

theorem frontier_profile_clip (R : ℝ) {n : ℕ} (U : Fin (n+1) → E) (k : ℕ) (w : E)
    (htail : ∀ i : Fin (n+1), k ≤ i.val → |⟪U i,Bilevel.RadialWrapper.compress R w⟫| ≤ 1/16) :
    frontierProfile R (clip U (k+1)) w = frontierProfile R U w ∧
      gradient (frontierProfile R (clip U (k+1))) w = gradient (frontierProfile R U) w := by
  have he : frontierProfile R (clip U (k+1)) =
      RadialWrapper.carried R (coordinates U) (fun z => Cutoffs.frontier (cutProjection (k+1) z)) := by
    funext x
    simp only [frontierProfile,RadialWrapper.carried,coordinates_clip,ContinuousLinearMap.comp_apply]
  rw [he]
  exact carried_frontier_truncated_value_gradient R k (coordinates U) w
    (by simpa only [coordinates_apply] using htail)

end Smoothness2601.FrameTruncation
