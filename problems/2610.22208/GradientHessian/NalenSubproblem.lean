import GradientHessian.NalenExtragradient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual compact trust-region subproblems. Symmetry suffices for the
derivative and necessary variational inequality; the quadratic need not
be convex and its Hessian norm is unrestricted. -/

noncomputable section
namespace GradientHessian.Nalen
open Set Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def quadraticModel (g : E) (B : E →L[ℝ] E) (δ v : E) (η : ℝ) (x : E) : ℝ :=
  ⟪g,x⟫_ℝ+(1/4 : ℝ)*⟪B (x-δ),x-δ⟫_ℝ+(1/(2*η))*‖x-v‖^2

theorem quadraticModel_continuous (g : E) (B : E →L[ℝ] E) (δ v : E) (η : ℝ) :
    Continuous (quadraticModel g B δ v η) := by
  unfold quadraticModel
  fun_prop

theorem quadraticModel_hasFDerivAt (g : E) (B : E →L[ℝ] E) (δ v : E) (η : ℝ)
    (hB : ∀ x y,⟪B x,y⟫_ℝ=⟪x,B y⟫_ℝ) (x : E) :
    HasFDerivAt (quadraticModel g B δ v η)
      (innerSL ℝ (g+(1/2 : ℝ) • B (x-δ)+(1/η) • (x-v))) x := by
  have hd : HasFDerivAt (fun y : E => y-δ) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const δ
  have hb := B.hasFDerivAt.comp x hd
  have h := (innerSL ℝ g).hasFDerivAt.add ((hb.inner ℝ hd).const_mul (1/4 : ℝ))
  have hv : HasFDerivAt (fun y : E => y-v) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const v
  have h' := h.add (hv.norm_sq.const_mul (1/(2*η)))
  convert h' using 1
  ext y
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,innerSL_apply,
    inner_add_left,real_inner_smul_left,smul_eq_mul,Function.comp_apply]
  have hi : ⟪B y,x-δ⟫_ℝ=⟪B (x-δ),y⟫_ℝ := by rw [hB]; exact real_inner_comm _ _
  rw [hi]
  ring

theorem quadraticModel_variational {D η : ℝ} (hη : 0 < η)
    (g : E) (B : E →L[ℝ] E) (δ v x : E)
    (hB : ∀ u w,⟪B u,w⟫_ℝ=⟪u,B w⟫_ℝ)
    (hx : x ∈ closedBall (0 : E) D)
    (hmin : IsMinOn (quadraticModel g B δ v η) (closedBall (0 : E) D) x)
    {u : E} (hu : u ∈ closedBall (0 : E) D) :
    0 ≤ ⟪η • (g+(1/2 : ℝ) • B (x-δ))+x-v,u-x⟫_ℝ := by
  have hi := hmin.localize.hasFDerivWithinAt_nonneg
    (quadraticModel_hasFDerivAt g B δ v η hB x).hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset ((convex_closedBall (0 : E) D).segment_subset hx hu))
  have hh := mul_nonneg hη.le hi
  simp only [innerSL_apply,inner_add_left,real_inner_smul_left] at hh
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left]
  have he : η*(1/η)=1 := by field_simp
  rw [mul_add,← mul_assoc,he,one_mul,inner_sub_left] at hh
  linarith only [hh]

theorem quadraticModel_exists_min [FiniteDimensional ℝ E] {D : ℝ} (hD : 0 ≤ D)
    (g : E) (B : E →L[ℝ] E) (δ v : E) (η : ℝ) :
    ∃ x ∈ closedBall (0 : E) D,
      IsMinOn (quadraticModel g B δ v η) (closedBall (0 : E) D) x :=
  (isCompact_closedBall (0 : E) D).exists_isMinOn ⟨0,by simpa using hD⟩
    (quadraticModel_continuous g B δ v η).continuousOn

/-- A genuine minimizer, used for the analytic recursion. Measurable oracle
implementations can use any selector satisfying the same minimum property. -/
def quadraticStep [FiniteDimensional ℝ E] {D : ℝ} (hD : 0 ≤ D)
    (g : E) (B : E →L[ℝ] E) (δ v : E) (η : ℝ) : E :=
  Classical.choose (quadraticModel_exists_min hD g B δ v η)

theorem quadraticStep_spec [FiniteDimensional ℝ E] {D : ℝ} (hD : 0 ≤ D)
    (g : E) (B : E →L[ℝ] E) (δ v : E) (η : ℝ) :
    quadraticStep hD g B δ v η ∈ closedBall (0 : E) D ∧
    IsMinOn (quadraticModel g B δ v η) (closedBall (0 : E) D)
      (quadraticStep hD g B δ v η) :=
  Classical.choose_spec (quadraticModel_exists_min hD g B δ v η)

theorem proximalModel_variational {D η : ℝ} (hη : 0 < η) (g v w : E)
    (hw : w ∈ closedBall (0 : E) D)
    (hmin : IsMinOn (quadraticModel g 0 0 v η) (closedBall (0 : E) D) w)
    {u : E} (hu : u ∈ closedBall (0 : E) D) :
    0 ≤ ⟪η • g+w-v,u-w⟫_ℝ := by
  simpa using quadraticModel_variational hη g 0 0 v w (by simp) hw hmin hu

/-- The one-step inequality follows from genuine minimization problems. -/
theorem minimizers_extragradient {D η : ℝ} (hη : 0 < η)
    (g g₀ : E) (B : E →L[ℝ] E) (δ v x w u : E)
    (hB : ∀ s t,⟪B s,t⟫_ℝ=⟪s,B t⟫_ℝ)
    (hx : x ∈ closedBall (0 : E) D) (hw : w ∈ closedBall (0 : E) D)
    (hu : u ∈ closedBall (0 : E) D)
    (hminx : IsMinOn (quadraticModel g₀ B δ v η) (closedBall (0 : E) D) x)
    (hminw : IsMinOn (quadraticModel g 0 0 v η) (closedBall (0 : E) D) w) :
    ⟪g,x-u⟫_ℝ ≤ ‖u-v‖^2/(2*η)-‖u-w‖^2/(2*η)+
      η*‖g₀+(1/2 : ℝ) • B (x-δ)-g‖^2-‖x-v‖^2/(2*η)-‖x-w‖^2/(4*η) :=
  extragradient_step hη g (g₀+(1/2 : ℝ) • B (x-δ)) x v w u
    (quadraticModel_variational hη g₀ B δ v x hB hx hminx hw)
    (proximalModel_variational hη g v w hw hminw hu)

end GradientHessian.Nalen
