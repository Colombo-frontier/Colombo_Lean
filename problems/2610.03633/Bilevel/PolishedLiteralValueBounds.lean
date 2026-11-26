import Bilevel.PolishedLiteralFormulas
import Bilevel.PolishedLiteralSize
import Bilevel.ChiBoundedChainReceiverBounds

/-! Actual uniform value estimates for the literal micro payload.  The
linear-growth penalty is controlled by the proved global chain gradient,
so the estimate applies globally after the common radial wrapper. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential RadialWrapper

theorem chain_value_control : ∃ C : ℝ,0≤C ∧
    ∀ (n : ℕ) (L β : ℝ),0≤L → 0<β → ∀ z : Space n,
      |chain n L β z|≤(L*β^2)*phi 0+C*(L*β)*Real.sqrt ((n:ℝ)+1)*‖z‖ := by
  obtain ⟨C,hC,hbound⟩ := chain_gradient_norm_uniform
  refine ⟨C,hC,fun n L β hL hβ z => ?_⟩
  have hd (y : Space n) := ((chain_contDiff n L β 1).differentiable (by norm_num) y).hasFDerivAt
  have hg (y : Space n) : ‖fderiv ℝ (chain n L β) y‖≤C*(L*β)*Real.sqrt ((n:ℝ)+1) := by
    rw [← GradientJetBounds.gradient_norm_eq]
    exact hbound n L β hL hβ y
  have ht : ‖chain n L β z-chain n L β 0‖≤
      (C*(L*β)*Real.sqrt ((n:ℝ)+1))*‖z-(0:Space n)‖ :=
    convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun v _ => (hd v).hasFDerivWithinAt) (fun v _ => hg v) (Set.mem_univ _) (Set.mem_univ _)
  have hz : chain n L β 0=-(L*β^2)*phi 0 := by
    simp only [chain,ZeroChainResidualScaled.scaled,smul_zero,value_zero]
    ring
  rw [Real.norm_eq_abs,sub_zero,hz] at ht
  have hi := abs_add (chain n L β z-chain n L β 0) (chain n L β 0)
  rw [sub_add_cancel,hz,abs_mul,abs_neg,abs_of_nonneg (show 0≤L*β^2 by positivity),
    abs_of_nonneg (phi_nonneg 0)] at hi
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem wrapped_micro_value_bound (C : ℝ)
    (hC : 0≤C)
    (hchain : ∀ (n : ℕ) (L β : ℝ),0≤L → 0<β → ∀ z : Space n,
      |chain n L β z|≤(L*β^2)*phi 0+C*(L*β)*Real.sqrt ((n:ℝ)+1)*‖z‖)
    (n : ℕ) (L b κ ζ Cu A : ℝ)
    (hL : 0<L) (hb : 0<b) (hκ : 0<κ) (hζ : 0<ζ) (hCu : 0<Cu) (hA : 0≤A)
    (hsize : Real.sqrt ((n:ℝ)+1)≤ζ^3*κ)
    (V : Space n →ₗᵢ[ℝ] E) (u : E) :
    |chain n L (b/κ) (WrappedChain.coordinates n (Cu*b/ζ) V u)+
      positiveReceiver A (ζ*L) (L*(b/κ)) (b/κ) b
        (WrappedChain.coordinates n (Cu*b/ζ) V u (Fin.last n))|≤
      (phi 0/κ^2+C*Cu*ζ^2+9*A*ζ+3*A/κ)*(L*b^2) := by
  let z := WrappedChain.coordinates n (Cu*b/ζ) V u
  have hβ : 0<b/κ := div_pos hb hκ
  have hR : 0<Cu*b/ζ := div_pos (mul_pos hCu hb) hζ
  have hz : ‖z‖≤Cu*b/ζ := (frame_adjoint_norm_le V _).trans (compress_norm_le_radius _ hR u)
  have hc := hchain n L (b/κ) hL.le hβ z
  have hd := positiveReceiver_abs_bound A (ζ*L) (L*(b/κ)) (b/κ) b (z (Fin.last n))
    hA (mul_nonneg hζ.le hL.le) (mul_nonneg hL.le hβ.le) hβ hb
  have hsz := mul_le_mul hsize hz (norm_nonneg _) (by positivity : 0≤ζ^3*κ)
  have hh := mul_le_mul_of_nonneg_left hsz (show 0≤C*(L*(b/κ)) by positivity)
  have ht := abs_add (chain n L (b/κ) z) (positiveReceiver A (ζ*L) (L*(b/κ)) (b/κ) b (z (Fin.last n)))
  have he : (L*(b/κ)^2)*phi 0+(C*(L*(b/κ)))*((ζ^3*κ)*(Cu*b/ζ))+
      (A*(3*(ζ*L)*b+L*(b/κ)))*(3*b)=
      (phi 0/κ^2+C*Cu*ζ^2+9*A*ζ+3*A/κ)*(L*b^2) := by
    field_simp
    ring
  change |chain n L (b/κ) z+positiveReceiver A (ζ*L) (L*(b/κ)) (b/κ) b (z (Fin.last n))|≤_
  rw [← he]
  nlinarith only [hc,hd,hh,ht]

end Bilevel.PolishedLiteral
