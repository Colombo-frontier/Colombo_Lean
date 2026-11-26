import Bilevel.PolishedLiteralUpperCertificate

/-! Exact kappa dilation of the source hyperobjective. The full joint
operator norm is at most kappa, yielding its actual C L kappa^2 bound. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def outerDilation (κ : ℝ) : Joint X U →L[ℝ] Joint X U :=
  (packLinear (X:=X) (Y:=U)).comp
    ((fstMap (X:=X) (U:=U)).prod (κ • sndMap (X:=X) (U:=U)))

omit [CompleteSpace X] [CompleteSpace U] in
theorem outerDilation_apply (κ : ℝ) (z : Joint X U) : outerDilation κ z=pack z.fst (κ • z.snd) := rfl

omit [CompleteSpace X] [CompleteSpace U] in
theorem outerDilation_norm (κ : ℝ) (hκ : 1≤κ) : ‖outerDilation (X:=X) (U:=U) κ‖≤κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro z
  rw [outerDilation_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤κ*‖z‖)).mp
  rw [norm_sq]
  change ‖z.fst‖^2+‖κ • z.snd‖^2≤(κ*‖z‖)^2
  rw [mul_pow,norm_sq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤κ),mul_pow]
  nlinarith [sq_nonneg ‖z.fst‖,sq_nonneg (κ-1),mul_nonneg (show 0≤κ^2-1 by nlinarith) (sq_nonneg ‖z.fst‖)]

namespace Parameters
variable (P : Parameters (X:=X) (U:=U))

theorem outerMean_second_bound (κ C : ℝ) (hκ : 1≤κ) (hC : 0≤C)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 P.meanBase z‖≤C) (z : Joint X U) :
    ‖iteratedFDeriv ℝ 2 (P.outerMean κ) z‖≤C*κ^2 := by
  have he : P.outerMean κ=P.meanBase ∘ outerDilation κ := rfl
  rw [he,(outerDilation κ).iteratedFDeriv_comp_right P.meanBase_contDiff z (by exact_mod_cast (show (2:ℕ)≤3 by omega))]
  have ht := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ 2 P.meanBase (outerDilation κ z)) (fun _ : Fin 2 => outerDilation (X:=X) (U:=U) κ)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at ht
  exact ht.trans (mul_le_mul (hb _) (pow_le_pow_left₀ (norm_nonneg _) (outerDilation_norm κ hκ) 2)
    (sq_nonneg _) hC)

theorem outerMean_gradient_lipschitz (κ C : ℝ) (hκ : 1≤κ) (hC : 0≤C)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 P.meanBase z‖≤C) (z z' : Joint X U) :
    ‖gradient (P.outerMean κ) z-gradient (P.outerMean κ) z'‖≤C*κ^2*‖z-z'‖ :=
  GradientJetBounds.gradient_lipschitz (P.outerMean_contDiff κ) (C*κ^2)
    (P.outerMean_second_bound κ C hκ hC hb) z z'

end Parameters
end Bilevel.PolishedLiteral
