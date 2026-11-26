import Bilevel.ScaledZeroChain
import Bilevel.WrapperEndgame

/-! The end-game gradient bound for the actual compressed, rotated zero chain.
The frame is a linear isometry, so every orthonormal frame is covered. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.WrappedChain
open ZeroChain RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def value (n : ℕ) (a β ν R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (u : E) : ℝ :=
  wrapped ν R (ScaledZeroChain.value n a β) U.toContinuousLinearMap.adjoint u

def coordinates (n : ℕ) (R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (u : E) : Space n :=
  U.toContinuousLinearMap.adjoint (compress R u)

def carriedGradient (n : ℕ) (a β R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (u : E) : E :=
  U (gradient (ScaledZeroChain.value n a β) (coordinates n R U u))

theorem value_hasGradientAt (n : ℕ) (a β ν R : ℝ) (hR : 0 < R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    HasGradientAt (value n a β ν R U) (wrappedGradient ν R u (carriedGradient n a β R U u)) u := by
  have h := wrapped_hasGradientAt ν R hR (ScaledZeroChain.value n a β)
    U.toContinuousLinearMap.adjoint u (gradient (ScaledZeroChain.value n a β) (coordinates n R U u))
    (by rw [ScaledZeroChain.actual_gradient]; exact ScaledZeroChain.value_hasGradientAt n a β _)
  simpa only [value, carriedGradient, ContinuousLinearMap.adjoint_adjoint,
    LinearIsometry.coe_toContinuousLinearMap] using h

theorem carriedGradient_norm_bound (n : ℕ) (a β R B : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (hB : 0 ≤ B) (hbound : ∀ (z : Space n) j, |gradient (ZeroChain.value n) z j| ≤ B)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) :
    ‖carriedGradient n a β R U u‖ ≤ a / β * B * Real.sqrt (n + 1 : ℕ) := by
  rw [carriedGradient, U.norm_map]
  exact ScaledZeroChain.gradient_norm_bound n a β B ha hβ hB hbound _

theorem frontier (n : ℕ) (a β R : ℝ) (ha : 0 ≤ a) (hβ : 0 < β)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hlast : |coordinates n R U u (Fin.last n)| < β) :
    ∃ w : E, ‖w‖ = 1 ∧ ⟪carriedGradient n a β R U u, w⟫ ≤ -(a / β) ∧
      |⟪compress R u, w⟫| ≤ β := by
  obtain ⟨j, hj, hg⟩ := ScaledZeroChain.frontier n a β ha hβ (coordinates n R U u) hlast
  refine ⟨U (basis j), ?_, ?_, ?_⟩
  · simp [U.norm_map, basis, EuclideanSpace.norm_single]
  · rw [carriedGradient, U.inner_map_map, real_inner_comm, inner_basis]
    exact hg
  · have he : ⟪compress R u, U (basis j)⟫ = coordinates n R U u j := by
      change ⟪compress R u, U.toContinuousLinearMap (basis j)⟫ = coordinates n R U u j
      rw [← ContinuousLinearMap.adjoint_inner_left U.toContinuousLinearMap (basis j),
        real_inner_comm, inner_basis]
      rfl
    rw [he]
    exact hj.le

theorem endgame (n : ℕ) (a β ν R B : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (hν : 0 ≤ ν) (hR : 0 < R) (hB : 0 ≤ B)
    (hbound : ∀ (z : Space n) j, |gradient (ZeroChain.value n) z j| ≤ B)
    (hinner : (ν + (a / β * B * Real.sqrt (n + 1 : ℕ)) / R) * β ≤ (a / β) / 6)
    (houter : (a / β) / 2 ≤ 2 * ν * R / 3 - a / β * B * Real.sqrt (n + 1 : ℕ))
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hlast : |coordinates n R U u (Fin.last n)| < β) :
    (a / β) / 2 ≤ ‖gradient (value n a β ν R U) u‖ := by
  rw [(value_hasGradientAt n a β ν R hR U u).gradient]
  apply wrapper_endgame ν R (a / β * B * Real.sqrt (n + 1 : ℕ)) β (a / β)
    hν hR (by positivity) (div_pos ha hβ) hinner houter u (carriedGradient n a β R U u)
    (carriedGradient_norm_bound n a β R B ha.le hβ hB hbound U u)
  intro _
  exact frontier n a β R ha.le hβ U u hlast

end Bilevel.WrappedChain
