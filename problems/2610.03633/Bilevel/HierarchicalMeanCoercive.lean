import Bilevel.HierarchicalMeanGap

/-! Coercivity of the exact additive mean after dilation in the lower
tangent variable. No property of frame-relative orientations is required. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Filter
open scoped Topology
namespace Bilevel.HierarchicalMean.Parameters
open PrimitiveGeometry RadialWrapper
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : Parameters (X:=X) (U:=U))

theorem meanBase_contDiff : ContDiff ℝ 3 P.meanBase := by
  have he : P.meanBase=fun z => P.upperBase z+P.selectedResidual z :=
    funext (fun z => (P.exact_cancellation z).symm)
  rw [he]
  exact P.upperBase_contDiff.add P.selectedResidual_contDiff

theorem objective_contDiff (κ : ℝ) : ContDiff ℝ 3 (P.objective κ) := by
  have hfst : ContDiff ℝ 3 (fun z : Joint X U => z.fst) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ X U).contDiff.fst
  have hsnd : ContDiff ℝ 3 (fun z : Joint X U => z.snd) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ X U).contDiff.snd
  exact P.meanBase_contDiff.comp ((packLinear (X:=X) (Y:=U)).contDiff.comp
    (hfst.prodMk (hsnd.const_smul κ)))

theorem objective_linear_lower (κ : ℝ) (hκ : 0<κ)
    (hℓ : 0≤P.macroNode.ell) (hL : 0≤P.L) (hA : 0≤P.receiver)
    (hν : 0<P.ν) (hmacro : 0<P.macroRadial) (hg : 0≤P.force)
    (hβ : 0<P.β) (hb : 0<P.macroNode.width)
    (hR : 0<P.radius) (hRM : 0<P.macroNode.radius) :
    ∃ a c : ℝ,0<a ∧ ∀ z : Joint X U,a*‖z‖-c≤P.objective κ z := by
  let a := min (P.macroRadial*P.macroNode.radius) (P.ν*P.radius*κ)
  let c := P.gapBudget+P.macroRadial*P.macroNode.radius^2+P.ν*P.radius^2
  have ha : 0<a := lt_min (mul_pos hmacro hRM) (mul_pos (mul_pos hν hR) hκ)
  refine ⟨a,c,ha,fun z => ?_⟩
  have hlow := P.meanBase_lower hℓ hL hA hν.le hg hβ hb (pack z.fst (κ • z.snd))
  change bowl P.macroRadial P.macroNode.radius z.fst+bowl P.ν P.radius (κ • z.snd)-
    P.gapBudget≤P.objective κ z at hlow
  have hx := bowl_linear_lower P.macroRadial P.macroNode.radius hmacro.le hRM z.fst
  have hu := bowl_linear_lower P.ν P.radius hν.le hR (κ • z.snd)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hκ] at hu
  have hax := mul_le_mul_of_nonneg_right (min_le_left (P.macroRadial*P.macroNode.radius)
    (P.ν*P.radius*κ)) (norm_nonneg z.fst)
  have hau := mul_le_mul_of_nonneg_right (min_le_right (P.macroRadial*P.macroNode.radius)
    (P.ν*P.radius*κ)) (norm_nonneg z.snd)
  have hn : ‖z‖≤‖z.fst‖+‖z.snd‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [norm_sq]
    nlinarith [mul_nonneg (norm_nonneg z.fst) (norm_nonneg z.snd)]
  have hna := mul_le_mul_of_nonneg_left hn ha.le
  change a*‖z.fst‖≤_ at hax
  change a*‖z.snd‖≤_ at hau
  dsimp only [c]
  nlinarith only [hlow,hx,hu,hax,hau,hna]

theorem objective_coercive [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
    (κ : ℝ) (hκ : 0<κ)
    (hℓ : 0≤P.macroNode.ell) (hL : 0≤P.L) (hA : 0≤P.receiver)
    (hν : 0<P.ν) (hmacro : 0<P.macroRadial) (hg : 0≤P.force)
    (hβ : 0<P.β) (hb : 0<P.macroNode.width)
    (hR : 0<P.radius) (hRM : 0<P.macroNode.radius) :
    Tendsto (P.objective κ) (cocompact (Joint X U)) atTop := by
  obtain ⟨a,c,ha,hbound⟩ := P.objective_linear_lower κ hκ hℓ hL hA hν hmacro hg hβ hb hR hRM
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_norm_cocompact_atTop (E:=Joint X U)).eventually_ge_atTop ((b+c)/a)
  filter_upwards [hn] with z hz
  have hh := (div_le_iff₀ ha).mp hz
  have hb := hbound z
  nlinarith only [hh,hb]

theorem objective_minimum_attained [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
    (κ : ℝ) (hκ : 0<κ)
    (hℓ : 0≤P.macroNode.ell) (hL : 0≤P.L) (hA : 0≤P.receiver)
    (hν : 0<P.ν) (hmacro : 0<P.macroRadial) (hg : 0≤P.force)
    (hβ : 0<P.β) (hb : 0<P.macroNode.width)
    (hR : 0<P.radius) (hRM : 0<P.macroNode.radius) :
    ∃ z : Joint X U,∀ w,P.objective κ z≤P.objective κ w :=
  (P.objective_contDiff κ).continuous.exists_forall_le
    (P.objective_coercive κ hκ hℓ hL hA hν hmacro hg hβ hb hR hRM)

end Bilevel.HierarchicalMean.Parameters
