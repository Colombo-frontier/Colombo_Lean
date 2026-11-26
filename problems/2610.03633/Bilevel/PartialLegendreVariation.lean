import Bilevel.PartialLegendreDerivative
import Bilevel.Curvature

/-! Actual inverse-Hessian variation and C2 regularity of the fixed-slice
conjugate. The inverse operators are constructed from the small perturbation;
the Hessian Lipschitz constant is inherited through the inverse solution. -/
noncomputable section
namespace Bilevel.PartialLegendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {δ : NNReal} (hδ : δ < 1)

theorem linearEquiv_inverse_difference_bound (B C : E →L[ℝ] E)
    (hB : ‖B‖ ≤ (δ:ℝ)) (hC : ‖C‖ ≤ (δ:ℝ)) :
    ‖((linearEquiv hδ B hB).symm : E →L[ℝ] E)-
      ((linearEquiv hδ C hC).symm : E →L[ℝ] E)‖ ≤
        (1-(δ:ℝ))⁻¹^2*‖B-C‖ := by
  have hd : 0 < 1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hb := linearEquiv_inverse_bound hδ B hB
  have hc := linearEquiv_inverse_bound hδ C hC
  simp only [one_div] at hb hc
  have hh := Curvature.inverse_difference_norm (linearPerturbation B) (linearPerturbation C)
    ((linearEquiv hδ B hB).symm : E →L[ℝ] E)
    ((linearEquiv hδ C hC).symm : E →L[ℝ] E)
    (fun v => (linearEquiv hδ B hB).symm_apply_apply v)
    (fun v => (linearEquiv hδ C hC).apply_symm_apply v) hd hb hc
  have he : linearPerturbation B-linearPerturbation C=B-C := by
    unfold linearPerturbation
    abel
  rwa [he] at hh

variable {G : E → E} (hG : LipschitzWith δ G)

def inverseHessian (B : E → E →L[ℝ] E) (hB : ∀ z,‖B z‖≤(δ:ℝ)) (y : E) : E →L[ℝ] E :=
  ((linearEquiv hδ (B (solution hδ hG y)) (hB _)).symm : E →L[ℝ] E)

theorem inverseHessian_variation (B : E → E →L[ℝ] E) (hB : ∀ z,‖B z‖≤(δ:ℝ))
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) (y w : E) :
    ‖inverseHessian hδ hG B hB y-inverseHessian hδ hG B hB w‖ ≤
      H/(1-(δ:ℝ))^3*‖y-w‖ := by
  have hd : 0 < 1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  calc
    _ ≤ (1-(δ:ℝ))⁻¹^2*‖B (solution hδ hG y)-B (solution hδ hG w)‖ :=
      linearEquiv_inverse_difference_bound hδ _ _ _ _
    _ ≤ (1-(δ:ℝ))⁻¹^2*(H*(‖y-w‖/(1-(δ:ℝ)))) := by
      gcongr
      exact (hLip _ _).trans (mul_le_mul_of_nonneg_left
        (solution_lipschitz_bound hδ hG y w) hH)
    _ = _ := by field_simp [ne_of_gt hd]; ring_nf; simp

theorem inverseHessian_continuous (B : E → E →L[ℝ] E) (hB : ∀ z,‖B z‖≤(δ:ℝ))
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    Continuous (inverseHessian hδ hG B hB) := by
  have hd : 0 < 1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hl : LipschitzWith ⟨H/(1-(δ:ℝ))^3,by positivity⟩ (inverseHessian hδ hG B hB) := by
    apply LipschitzWith.of_dist_le_mul
    intro y w
    simpa only [dist_eq_norm,NNReal.coe_mk] using inverseHessian_variation hδ hG B hB hH hLip y w
  exact hl.continuous

theorem solution_contDiff_one (B : E → E →L[ℝ] E) (hB : ∀ z,‖B z‖≤(δ:ℝ))
    (hDG : ∀ z,HasFDerivAt G (B z) z)
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ContDiff ℝ 1 (solution hδ hG) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨inverseHessian hδ hG B hB,inverseHessian_continuous hδ hG B hB hH hLip,
    fun y => solution_hasFDerivAt hδ hG y _ (hB _) (hDG _)⟩

theorem conjugate_contDiff_two (P : E → ℝ) (hP : ∀ z,HasGradientAt P (G z) z)
    (B : E → E →L[ℝ] E) (hB : ∀ z,‖B z‖≤(δ:ℝ))
    (hDG : ∀ z,HasFDerivAt G (B z) z)
    {H : ℝ} (hH : 0≤H) (hLip : ∀ z w,‖B z-B w‖≤H*‖z-w‖) :
    ContDiff ℝ 2 (conjugate hδ hG P) := by
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => InnerProductSpace.toDual ℝ E (solution hδ hG y),?_,?_⟩
  · exact (InnerProductSpace.toDual ℝ E).contDiff.comp
      (solution_contDiff_one hδ hG B hB hDG hH hLip)
  · intro y
    exact (conjugate_hasGradientAt hδ hG P hP y).hasFDerivAt

end Bilevel.PartialLegendre
