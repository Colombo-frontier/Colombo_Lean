import Smoothness2601.SineAdmissible
import Smoothness2601.ChainWrapper

/-! Dimension-independent fixed constants for the actual wrapped split chain.
The constants are defined before the ambient space and frame are introduced. -/
noncomputable section
namespace Smoothness2601.HardProfiles
open SineGeometry ExtensiveChain Cutoffs

def scalarBound : ℝ := Classical.choose (actual_profile_control_exists chainAmplitude_nonneg)
theorem scalarBound_control : ActualProfileControl chainAmplitude scalarBound :=
  Classical.choose_spec (actual_profile_control_exists chainAmplitude_nonneg)
def radiusConstant : ℝ := max 1 (scalarBound+4*scalarBound^2+frontierGradientBound)
def upperSmoothness : ℝ := scalarBound+8*scalarBound^2+1/8
def frontierSmoothness : ℝ := frontierHessianBound+1/16
def gapConstant : ℝ := 2*(scalarBound+2*scalarBound^2)+1/2

theorem radiusConstant_ge_one : 1 ≤ radiusConstant := le_max_left _ _
theorem radiusConstant_large : scalarBound+4*scalarBound^2+frontierGradientBound ≤ radiusConstant :=
  le_max_right _ _
theorem upperSmoothness_nonneg : 0 ≤ upperSmoothness := by
  unfold upperSmoothness
  nlinarith [scalarBound_control.nonnegative]
theorem frontierSmoothness_nonneg : 0 ≤ frontierSmoothness := by
  unfold frontierSmoothness
  linarith [frontierHessianBound_nonneg]
theorem gapConstant_pos : 0 < gapConstant := by
  unfold gapConstant
  nlinarith [scalarBound_control.nonnegative]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_differentiable {f : E → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) := by
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (by norm_num))
  exact hg.differentiable (by norm_num)

def profiles {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : Profiles E where
  A := wrappedA radiusConstant chainAmplitude U
  B := wrappedB radiusConstant U
  gA := gradient (wrappedA radiusConstant chainAmplitude U)
  gB := gradient (wrappedB radiusConstant U)
  LA := upperSmoothness
  C₀ := 1/4
  C₁ := frontierGradientBound
  C₂ := frontierSmoothness
  LA_nonneg := upperSmoothness_nonneg
  C₀_nonneg := by norm_num
  C₁_nonneg := frontierGradientBound_nonneg
  C₂_nonneg := frontierSmoothness_nonneg
  has_A := fun x => ((wrappedA_contDiff radiusConstant chainAmplitude U 1).differentiable (by norm_num) x).hasGradientAt
  has_B := fun x => ((wrappedB_contDiff radiusConstant U 1).differentiable (by norm_num) x).hasGradientAt
  bound_B := fun x => (wrapped_split_uniform_bounds scalarBound_control radiusConstant_ge_one radiusConstant_large U x).1
  bound_gB := fun x => (wrapped_split_uniform_bounds scalarBound_control radiusConstant_ge_one radiusConstant_large U x).2.1
  lip_gA := fun x z => Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun v (_ : v ∈ Set.univ) => gradient_differentiable (wrappedA_contDiff radiusConstant chainAmplitude U 2) v)
    (fun v (_ : v ∈ Set.univ) =>
      (wrapped_split_uniform_bounds scalarBound_control radiusConstant_ge_one radiusConstant_large U v).2.2.2)
    convex_univ (Set.mem_univ z) (Set.mem_univ x)
  lip_gB := fun x z => Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun v (_ : v ∈ Set.univ) => gradient_differentiable (wrappedB_contDiff radiusConstant U 2) v)
    (fun v (_ : v ∈ Set.univ) =>
      (wrapped_split_uniform_bounds scalarBound_control radiusConstant_ge_one radiusConstant_large U v).2.2.1)
    convex_univ (Set.mem_univ z) (Set.mem_univ x)

theorem profiles_B_zero {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : (profiles U).B 0 = 0 := by
  have hb : bump 0 = 0 := bump_identity (by norm_num)
  simp [profiles,wrappedB,RadialWrapper.carried,Bilevel.RadialWrapper.compress,
    Cutoffs.frontier,BoundedFrontier.frontier,BoundedFrontier.summand,hb]

theorem profiles_gradient_sum {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (w : E) :
    (profiles U).gA w+(profiles U).gB w = gradient (wrappedH radiusConstant chainAmplitude U) w := by
  have he : wrappedH radiusConstant chainAmplitude U = fun w => (profiles U).A w+(profiles U).B w :=
    funext fun w => wrappedH_split _ _ U w
  rw [he]
  apply Eq.symm
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [map_add] using ((profiles U).has_A w).hasFDerivAt.add ((profiles U).has_B w).hasFDerivAt

theorem profiles_barrier {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (w : E)
    (hh : ∃ j : Fin (n+1), |frameProjection U (Bilevel.RadialWrapper.compress (chainRadius radiusConstant n) w) j| < 1) :
    (1/2:ℝ) ≤ ‖(profiles U).gA w+(profiles U).gB w‖ := by
  rw [profiles_gradient_sum]
  exact wrapped_chain_gradient_barrier chainAmplitude_nonneg le_rfl radiusConstant_ge_one U
    (fun z => (chain_gradient_bound scalarBound_control z).trans
      (mul_le_mul_of_nonneg_right radiusConstant_large (Real.sqrt_nonneg _))) w hh

theorem profiles_gap {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (w : E) :
    (profiles U).A 0+(profiles U).B 0-((profiles U).A w+(profiles U).B w) ≤ gapConstant*(n+1) := by
  change wrappedA radiusConstant chainAmplitude U 0+wrappedB radiusConstant U 0-
    (wrappedA radiusConstant chainAmplitude U w+wrappedB radiusConstant U w) ≤ gapConstant*(n+1)
  rw [← wrappedH_split,← wrappedH_split]
  exact wrapped_initial_gap_bound scalarBound_control U w

end Smoothness2601.HardProfiles
