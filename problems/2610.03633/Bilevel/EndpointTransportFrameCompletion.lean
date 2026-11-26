import Bilevel.ChiVirtualInclusion
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent endpoint prefix frames can be completed as rotations of
one common latent frame. No equality of source/target prefix lengths is
required, and the original query embeds with zero auxiliary coordinates. -/
noncomputable section
set_option autoImplicit false
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation
variable {E A V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem frame_rotation_exists {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (U T : W →ₗᵢ[ℝ] V) : ∃ Q : V ≃ₗᵢ[ℝ] V,∀ x,Q (U x)=T x := by
  let L : LinearMap.range U.toLinearMap →ₗᵢ[ℝ] V := T.comp U.equivRange.symm.toLinearIsometry
  let S : V →ₗᵢ[ℝ] V := L.extend
  have hs : Function.Surjective S := (LinearMap.injective_iff_surjective (f:=S.toLinearMap)).mp S.injective
  refine ⟨LinearIsometryEquiv.ofSurjective S hs,?_⟩
  intro x
  change L.extend (U x)=T x
  have he := L.extend_apply (U.equivRange x)
  change L.extend (U x)=T (U.equivRange.symm (U.equivRange x)) at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

omit [CompleteSpace E] [CompleteSpace A] in
theorem prefix_rotations_exist [FiniteDimensional ℝ E] [FiniteDimensional ℝ A]
    {ι : Type*} (n : ℕ) (r : ι → ℕ) (columns : ι → Fin (n+1) → E)
    (U : Space n →ₗᵢ[ℝ] Joint E A) (aux : Space n →ₗᵢ[ℝ] A)
    (hGram : ∀ i,∀ a b : Fin (n+1),a.val<r i → b.val<r i →
      ⟪columns i a,columns i b⟫=if a=b then 1 else 0) :
    ∃ Q : ι → (Joint E A ≃ₗᵢ[ℝ] Joint E A),
      ∀ i k,Q i (U (basis k))=completedColumn n (r i) (columns i) aux k := by
  classical
  choose Q hQ using fun i => frame_rotation_exists U (completionFrame n (r i) (columns i) aux (hGram i))
  exact ⟨Q,fun i k => (hQ i (basis k)).trans (completionFrame_basis n (r i) (columns i) aux (hGram i) k)⟩

end Bilevel.EndpointTransportResponse


