import SampleReuse.CurvatureScaleParameters
import SampleReuse.RadialAdmissible

open SecondOrder Filter
open scoped Topology

namespace SampleReuse
noncomputable section

def curvatureScaleK (P : Parameters) : ℝ :=
  1+4*curvatureKappa*curvatureCoreConstant/P.hessianLip
def curvatureWallSlope (P : Parameters) : ℝ := P.gradientBound/4
def curvatureRadiusScale (P : Parameters) : ℝ := 1+2*curvatureWallSlope P
def curvatureRadius (P : Parameters) (γ : ℝ) : ℝ := curvatureRadiusScale P/γ
def curvatureGradientConstant (P : Parameters) : ℝ :=
  curvatureCoreConstant*Real.sqrt (curvatureKappa*P.gap/8)
def curvatureHessianConstant : ℝ := curvatureKappa*curvatureCoreConstant
def curvatureThirdConstant (P : Parameters) : ℝ :=
  curvatureKappa/curvatureScaleK P*curvatureCoreConstant

theorem curvatureScaleK_pos (P : Parameters) : 0 < curvatureScaleK P := by
  have hκ := curvatureKappa_pos
  have hC := curvatureCoreConstant_pos
  have hL := P.hessianLip_pos
  unfold curvatureScaleK
  positivity

theorem curvatureWallSlope_pos (P : Parameters) : 0 < curvatureWallSlope P :=
  div_pos P.gradientBound_pos (by norm_num)

theorem curvatureRadiusScale_pos (P : Parameters) : 0 < curvatureRadiusScale P := by
  have hb := curvatureWallSlope_pos P
  unfold curvatureRadiusScale
  positivity

theorem curvatureGradientConstant_nonneg (P : Parameters) : 0 ≤ curvatureGradientConstant P :=
  mul_nonneg curvatureCoreConstant_pos.le (Real.sqrt_nonneg _)

theorem curvatureHessianConstant_pos : 0 < curvatureHessianConstant :=
  mul_pos curvatureKappa_pos curvatureCoreConstant_pos

theorem curvatureThirdConstant_pos (P : Parameters) : 0 < curvatureThirdConstant P :=
  mul_pos (div_pos curvatureKappa_pos (curvatureScaleK_pos P)) curvatureCoreConstant_pos

theorem curvatureThirdConstant_small (P : Parameters) : curvatureThirdConstant P < P.hessianLip/4 := by
  have hL := P.hessianLip_pos
  have hK := curvatureScaleK_pos P
  rw [curvatureThirdConstant, div_mul_eq_mul_div]
  apply (div_lt_iff₀ hK).mpr
  have he : P.hessianLip/4*curvatureScaleK P =
      P.hessianLip/4+curvatureKappa*curvatureCoreConstant := by
    unfold curvatureScaleK
    field_simp
    ring
  rw [he]
  linarith

def curvatureJetBudget (P : Parameters) (γ : ℝ) : ℕ → ℝ
  | 0 => P.gap/2
  | 1 => curvatureGradientConstant P*Real.sqrt γ
  | 2 => curvatureHessianConstant*γ
  | _ => curvatureThirdConstant P

def curvatureGlobalGradientBudget (P : Parameters) (γ : ℝ) : ℝ :=
  curvatureGradientConstant P*Real.sqrt γ+
    (γ/curvatureRadiusScale P)*cutoffRadialConstant 1*(P.gap/2)+curvatureWallSlope P

def curvatureGlobalSecondBudget (P : Parameters) (γ : ℝ) : ℝ :=
  curvatureHessianConstant*γ+
    2*((γ/curvatureRadiusScale P)*cutoffRadialConstant 1)*
      (curvatureGradientConstant P*Real.sqrt γ)+
    (γ/curvatureRadiusScale P)^2*cutoffRadialConstant 2*(P.gap/2)+
    curvatureWallSlope P*(γ/curvatureRadiusScale P)*wallRadialConstant 2

def curvatureGlobalThirdBudget (P : Parameters) (γ : ℝ) : ℝ :=
  curvatureThirdConstant P+
    3*((γ/curvatureRadiusScale P)*cutoffRadialConstant 1)*(curvatureHessianConstant*γ)+
    3*((γ/curvatureRadiusScale P)^2*cutoffRadialConstant 2)*
      (curvatureGradientConstant P*Real.sqrt γ)+
    (γ/curvatureRadiusScale P)^3*cutoffRadialConstant 3*(P.gap/2)+
    curvatureWallSlope P*(γ/curvatureRadiusScale P)^2*wallRadialConstant 3

def curvatureTransverseRatio (P : Parameters) (γ : ℝ) : ℝ :=
  4*curvatureHessianConstant*curvatureScaleK P/curvatureRadiusScale P*γ^2

theorem curvature_budget_identities (P : Parameters) {γ : ℝ} (hγ : 0 < γ) :
    radialGradientBudget (curvatureWallSlope P) (curvatureRadius P γ) (curvatureJetBudget P γ) =
      curvatureGlobalGradientBudget P γ ∧
    radialSecondBudget (curvatureWallSlope P) (curvatureRadius P γ) (curvatureJetBudget P γ) =
      curvatureGlobalSecondBudget P γ ∧
    radialThirdBudget (curvatureWallSlope P) (curvatureRadius P γ) (curvatureJetBudget P γ) =
      curvatureGlobalThirdBudget P γ := by
  have hR := (curvatureRadiusScale_pos P).ne'
  simp only [radialGradientBudget,radialSecondBudget,radialThirdBudget,
    curvatureGlobalGradientBudget,curvatureGlobalSecondBudget,curvatureGlobalThirdBudget,
    curvatureJetBudget,curvatureRadius, inv_div]
  constructor
  · trivial
  constructor <;> field_simp <;> ring

/-- A positive tolerance threshold satisfies all model and geometric budgets;
its constants depend only on the fixed model parameters, not frame or dimension. -/
theorem curvature_small_tolerance_budgets (P : Parameters) :
    ∃ η : ℝ, 0 < η ∧ ∀ γ : ℝ, 0 < γ → γ < η →
      curvatureGlobalGradientBudget P γ < P.gradientBound ∧
      curvatureGlobalSecondBudget P γ < P.gradientLip ∧
      curvatureGlobalThirdBudget P γ < P.hessianLip ∧
      curvatureGradientConstant P*Real.sqrt γ < P.gradientBound/8 ∧
      curvatureTransverseRatio P γ < 1 := by
  have hG : Continuous (curvatureGlobalGradientBudget P) := by
    unfold curvatureGlobalGradientBudget
    fun_prop
  have hS : Continuous (curvatureGlobalSecondBudget P) := by
    unfold curvatureGlobalSecondBudget
    fun_prop
  have hT : Continuous (curvatureGlobalThirdBudget P) := by
    unfold curvatureGlobalThirdBudget
    fun_prop
  have hB : Continuous (fun γ : ℝ => curvatureGradientConstant P*Real.sqrt γ) := by fun_prop
  have hX : Continuous (curvatureTransverseRatio P) := by
    unfold curvatureTransverseRatio
    fun_prop
  have eG : ∀ᶠ γ in 𝓝 (0:ℝ), curvatureGlobalGradientBudget P γ < P.gradientBound :=
    hG.continuousAt.eventually (gt_mem_nhds (by
      simp only [curvatureGlobalGradientBudget,Real.sqrt_zero,mul_zero,zero_div,zero_mul,
        zero_add,curvatureWallSlope]
      linarith [P.gradientBound_pos]))
  have eS : ∀ᶠ γ in 𝓝 (0:ℝ), curvatureGlobalSecondBudget P γ < P.gradientLip :=
    hS.continuousAt.eventually (gt_mem_nhds (by
      simpa [curvatureGlobalSecondBudget] using P.gradientLip_pos))
  have eT : ∀ᶠ γ in 𝓝 (0:ℝ), curvatureGlobalThirdBudget P γ < P.hessianLip :=
    hT.continuousAt.eventually (gt_mem_nhds (by
      simp only [curvatureGlobalThirdBudget,Real.sqrt_zero,mul_zero,zero_div,zero_mul,
        zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),add_zero]
      linarith [curvatureThirdConstant_small P,P.hessianLip_pos]))
  have eB : ∀ᶠ γ in 𝓝 (0:ℝ), curvatureGradientConstant P*Real.sqrt γ < P.gradientBound/8 :=
    hB.continuousAt.eventually (gt_mem_nhds (by simpa using
      (div_pos P.gradientBound_pos (by norm_num : (0:ℝ)<8))))
  have eX : ∀ᶠ γ in 𝓝 (0:ℝ), curvatureTransverseRatio P γ < 1 :=
    hX.continuousAt.eventually (gt_mem_nhds (by norm_num [curvatureTransverseRatio]))
  have hall := eG.and (eS.and (eT.and (eB.and eX)))
  obtain ⟨η,hη,hh⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨η,hη,fun γ hγ hγη => hh ?_⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_pos hγ] using hγη

end
end SampleReuse
