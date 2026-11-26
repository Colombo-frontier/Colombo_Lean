import Bilevel.NearIdentityMinimizer

/-! The actual convex conjugate of a quadratic plus a small smooth perturbation.
The inverse is constructed, the supremum is attained, and the conjugate's
gradient is derived from its value function rather than assumed. -/
noncomputable section
open scoped RealInnerProductSpace Topology
open Filter Asymptotics
namespace Bilevel.PartialLegendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {δ : NNReal} (hδ : δ < 1) {G : E → E} (hG : LipschitzWith δ G)

def solution (y : E) : E := NearIdentityInverse.inverse hδ hG y ⟨1,by norm_num⟩

def primal (P : E → ℝ) (z : E) : ℝ := ‖z‖^2/2+P z

def conjugate (P : E → ℝ) (y : E) : ℝ :=
  ⟪y,solution hδ hG y⟫-primal P (solution hδ hG y)

theorem solution_equation (y : E) : solution hδ hG y+G (solution hδ hG y)=y := by
  simpa only [solution,one_smul] using
    NearIdentityInverse.inverse_equation hδ hG y ⟨1,by norm_num⟩

theorem solution_of_equation (y z : E) (hz : z+G z=y) : z=solution hδ hG y :=
  NearIdentityInverse.inverse_unique hδ hG y z ⟨1,by norm_num⟩ (by simpa only [one_smul] using hz)

theorem solution_lipschitz_bound (y w : E) :
    ‖solution hδ hG y-solution hδ hG w‖ ≤ ‖y-w‖/(1-(δ:ℝ)) := by
  have hy := solution_equation hδ hG y
  have hw := solution_equation hδ hG w
  have he : solution hδ hG y-solution hδ hG w =
      (y-w)-(G (solution hδ hG y)-G (solution hδ hG w)) := by
    calc
      _ = ((solution hδ hG y+G (solution hδ hG y))-
        (solution hδ hG w+G (solution hδ hG w)))-
          (G (solution hδ hG y)-G (solution hδ hG w)) := by abel
      _ = _ := by rw [hy,hw]
  have ht := norm_sub_le (y-w) (G (solution hδ hG y)-G (solution hδ hG w))
  rw [← he] at ht
  have hl := hG.dist_le_mul (solution hδ hG y) (solution hδ hG w)
  rw [dist_eq_norm,dist_eq_norm] at hl
  have hd : 0 < 1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem solution_continuous : Continuous (solution hδ hG) := by
  have hd : 0 < 1-(δ:ℝ) := sub_pos.mpr (show (δ:ℝ)<1 from hδ)
  have hc : 0 ≤ 1/(1-(δ:ℝ)) := by positivity
  have hl : LipschitzWith ⟨1/(1-(δ:ℝ)),hc⟩ (solution hδ hG) := by
    apply LipschitzWith.of_dist_le_mul
    intro y w
    simpa only [dist_eq_norm,NNReal.coe_mk,one_div,div_eq_mul_inv,one_mul,mul_comm] using
      solution_lipschitz_bound hδ hG y w
  exact hl.continuous

variable (P : E → ℝ) (hP : ∀ z,HasGradientAt P (G z) z)
include hP

theorem conjugate_maximizes (y z : E) : ⟪y,z⟫-primal P z ≤ conjugate hδ hG P y := by
  have hh := NearIdentityInverse.inverse_minimizes hδ P hP hG y z ⟨1,by norm_num⟩
  change ‖solution hδ hG y‖^2/2+1*P (solution hδ hG y)-⟪y,solution hδ hG y⟫ ≤
    ‖z‖^2/2+1*P z-⟪y,z⟫ at hh
  unfold conjugate primal
  linarith

theorem conjugate_eq_supremum (y : E) :
    conjugate hδ hG P y = sSup (Set.range (fun z => ⟪y,z⟫-primal P z)) := by
  have hbounded : BddAbove (Set.range (fun z => ⟪y,z⟫-primal P z)) :=
    ⟨conjugate hδ hG P y,by rintro _ ⟨z,rfl⟩; exact conjugate_maximizes hδ hG P hP y z⟩
  apply le_antisymm
  · exact le_csSup hbounded ⟨solution hδ hG y,rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨z,rfl⟩
    exact conjugate_maximizes hδ hG P hP y z

theorem conjugate_subgradient (y w : E) :
    conjugate hδ hG P y+⟪solution hδ hG y,w-y⟫ ≤ conjugate hδ hG P w := by
  have hh := conjugate_maximizes hδ hG P hP w (solution hδ hG y)
  unfold conjugate at *
  have hcw : ⟪solution hδ hG y,w⟫ = ⟪w,solution hδ hG y⟫ := real_inner_comm _ _
  have hcy : ⟪solution hδ hG y,y⟫ = ⟪y,solution hδ hG y⟫ := real_inner_comm _ _
  rw [inner_sub_right,hcw,hcy]
  linarith

theorem conjugate_remainder (y d : E) :
    ‖conjugate hδ hG P (y+d)-conjugate hδ hG P y-⟪solution hδ hG y,d⟫‖ ≤
      (1/(1-(δ:ℝ)))*‖d‖^2 := by
  have hlo := conjugate_subgradient hδ hG P hP y (y+d)
  have hhi := conjugate_subgradient hδ hG P hP (y+d) y
  rw [add_sub_cancel_left] at hlo
  have he : y-(y+d) = -d := by abel
  rw [he,inner_neg_right] at hhi
  have hn : ‖⟪solution hδ hG (y+d)-solution hδ hG y,d⟫‖ ≤
      ‖solution hδ hG (y+d)-solution hδ hG y‖*‖d‖ := norm_inner_le_norm _ _
  have hsol := solution_lipschitz_bound hδ hG (y+d) y
  rw [add_sub_cancel_left] at hsol
  have hm := mul_le_mul_of_nonneg_right hsol (norm_nonneg d)
  have hb : ⟪solution hδ hG (y+d),d⟫-⟪solution hδ hG y,d⟫ ≤
      (1/(1-(δ:ℝ)))*‖d‖^2 := by
    rw [← inner_sub_left]
    exact (le_abs_self _).trans (hn.trans (by convert hm using 1; ring))
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  linarith

theorem conjugate_hasGradientAt (y : E) :
    HasGradientAt (conjugate hδ hG P) (solution hδ hG y) y := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply IsBigO.trans_isLittleO _ (isLittleO_norm_pow_id (E' := E) one_lt_two)
  apply IsBigO.of_bound (1/(1-(δ:ℝ)))
  apply Filter.Eventually.of_forall
  intro d
  change ‖conjugate hδ hG P (y+d)-conjugate hδ hG P y-⟪solution hδ hG y,d⟫‖ ≤
    (1/(1-(δ:ℝ)))*‖‖d‖^2‖
  rw [Real.norm_of_nonneg (sq_nonneg ‖d‖)]
  exact conjugate_remainder hδ hG P hP y d

theorem conjugate_gradient (y : E) : gradient (conjugate hδ hG P) y = solution hδ hG y :=
  (conjugate_hasGradientAt hδ hG P hP y).gradient

end Bilevel.PartialLegendre
