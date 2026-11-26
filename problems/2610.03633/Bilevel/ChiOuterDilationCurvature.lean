import Bilevel.ChiFixedDepthCurvature
import Bilevel.PartialLegendreJoint
import Bilevel.GradientJetBounds

/-! The actual inner-variable dilation pays exactly a quadratic operator
norm factor in the full objective curvature. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 250000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def innerDilation (m : ℕ) (K : ℝ) : Joint E (Blocks m F) →L[ℝ] Joint E (Blocks m F) :=
  packLinear.comp ((outerProjection (E:=E) (F:=F) m).prod (K • innerProjection (E:=E) (F:=F) m))

omit [CompleteSpace E] [CompleteSpace F] in
theorem innerDilation_norm (m : ℕ) (K : ℝ) : ‖innerDilation (E:=E) (F:=F) m K‖≤1+|K| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖pack z.fst (K • z.snd)‖≤_
  have hh := PartialLegendre.norm_pack_le_add z.fst (K • z.snd)
  rw [norm_smul,Real.norm_eq_abs] at hh
  have ha := WithLp.norm_fst_le E z
  have hb := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E z) (abs_nonneg K)
  nlinarith only [hh,ha,hb]

theorem jointOuter_dilation (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ) :
    jointOuter m M ν D ρ R d K=(jointOuter m M ν D ρ R d 1) ∘ innerDilation m K := by
  funext z
  change outerObjective M ν D ρ R d z.fst (padded (K • z.snd))=
    outerObjective M ν D ρ R d z.fst (padded (1 • (K • z.snd)))
  rw [one_smul]

theorem jointOuter_curvature_of_second (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) (K B : ℝ) (hB : 0≤B)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 (jointOuter m M ν D ρ R d 1) z‖≤B) :
    ∀ x z,‖gradient (jointOuter m M ν D ρ R d K) x-gradient (jointOuter m M ν D ρ R d K) z‖≤
      (B*(1+|K|)^2)*‖x-z‖ := by
  apply GradientJetBounds.gradient_lipschitz (jointOuter_contDiff m M ν D ρ R d K 3)
  intro z
  rw [jointOuter_dilation]
  rw [(innerDilation m K).iteratedFDeriv_comp_right (jointOuter_contDiff m M ν D ρ R d 1 3) z (by exact_mod_cast (show (2:ℕ)≤3 by omega))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul (hb _) (pow_le_pow_left₀ (norm_nonneg _) (innerDilation_norm m K) 2)
    (sq_nonneg _) hB

theorem jointOuter_kappa_curvature (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F)
    (ρ R : ℕ → ℝ) (d : ℕ) {κ B : ℝ} (hκ : 2≤κ) (hB : 0≤B)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 (jointOuter m M ν D ρ R d 1) z‖≤B) :
    ∀ x z,‖gradient (jointOuter m M ν D ρ R d (κ/6)) x-gradient (jointOuter m M ν D ρ R d (κ/6)) z‖≤
      (B*κ^2)*‖x-z‖ := by
  intro x z
  have hh := jointOuter_curvature_of_second m M ν D ρ R d (κ/6) B hB hb x z
  have hk : 0≤κ/6 := by linarith
  rw [abs_of_nonneg hk] at hh
  have hs : (1+κ/6)^2≤κ^2 := by nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hB) (norm_nonneg _))

end Bilevel.ChiOuter
