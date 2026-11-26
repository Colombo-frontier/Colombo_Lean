import SecondOrder.DependentReverseSelector
import SecondOrder.ScalarJetAlgebra
import SecondOrder.FiniteMeanCalculus

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {n : ℕ} {E : Fin n → Type*} {Ω : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

theorem dependentReverseSelector_contDiff (p : (i : Fin n) → E i → ℝ)
    (V : ℕ → PiLp 2 E → ℝ) {k : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ k (p i)) (hV : ∀ j ≤ n, ContDiff ℝ k (V j)) :
    ContDiff ℝ k (dependentReverseSelector p V) := by
  rw [dependentReverseSelector_eq_mixture]
  exact contDiff_bernoulliMixture _ _
    (fun i => (hp i).comp (dependentBlockProj (E := E) i).contDiff)
    (fun w => hV _ (lastSuccess_le w))

theorem dependentReverseSelector_pmfMean_zero [Fintype Ω] (P : PMF Ω)
    (p : (i : Fin n) → E i → ℝ) (V : Ω → ℕ → PiLp 2 E → ℝ)
    (x : PiLp 2 E)
    (hV : ∀ j ≤ n, pmfMean P (fun z => V z j x) = 0) :
    pmfMean P (fun z => dependentReverseSelector p (V z) x) = 0 := by
  simp only [dependentReverseSelector_eq_mixture, bernoulliMixture]
  rw [pmfMean_finset_sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [pmfMean_mul, hV _ (lastSuccess_le w), mul_zero]

/-- One random scalar function; the coefficient law is fixed independently of
the query. The selector weights are differentiated as part of this function. -/
def dependentConservativeLoss (F : PiLp 2 E → ℝ)
    (p : (i : Fin n) → E i → ℝ) (V : Ω → ℕ → PiLp 2 E → ℝ)
    (z : Ω) (x : PiLp 2 E) : ℝ := F x+dependentReverseSelector p (V z) x

theorem dependentConservativeLoss_contDiff (F : PiLp 2 E → ℝ)
    (p : (i : Fin n) → E i → ℝ) (V : Ω → ℕ → PiLp 2 E → ℝ)
    {k : WithTop ℕ∞} (hF : ContDiff ℝ k F) (hp : ∀ i, ContDiff ℝ k (p i))
    (hV : ∀ z j, j ≤ n → ContDiff ℝ k (V z j)) (z : Ω) :
    ContDiff ℝ k (dependentConservativeLoss F p V z) :=
  hF.add (dependentReverseSelector_contDiff p (V z) hp (hV z))

theorem dependentConservativeLoss_mean [Fintype Ω] (P : PMF Ω)
    (F : PiLp 2 E → ℝ) (p : (i : Fin n) → E i → ℝ)
    (V : Ω → ℕ → PiLp 2 E → ℝ)
    (hV : ∀ x j, j ≤ n → pmfMean P (fun z => V z j x) = 0)
    (x : PiLp 2 E) :
    pmfMean P (fun z => dependentConservativeLoss F p V z x) = F x := by
  unfold dependentConservativeLoss
  rw [pmfMean_add, pmfMean_const,
    dependentReverseSelector_pmfMean_zero P p V x (hV x), add_zero]

end
noncomputable section
variable {n : ℕ} {E : Fin n → Type*} {Ω : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]
  [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Exact unbiasedness of the value, gradient, and Hessian of the same sampled loss. -/
theorem dependentConservativeLoss_unbiased (P : PMF Ω)
    (F : PiLp 2 E → ℝ) (p : (i : Fin n) → E i → ℝ)
    (V : Ω → ℕ → PiLp 2 E → ℝ)
    (hF : ContDiff ℝ 2 F) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (hV : ∀ z j, j ≤ n → ContDiff ℝ 2 (V z j))
    (hmean : ∀ x j, j ≤ n → pmfMean P (fun z => V z j x) = 0)
    (x : PiLp 2 E) :
    (∫ z, dependentConservativeLoss F p V z x ∂P.toMeasure) = F x ∧
    (∫ z, gradient (dependentConservativeLoss F p V z) x ∂P.toMeasure) = gradient F x ∧
    (∫ z, fderiv ℝ (gradient (dependentConservativeLoss F p V z)) x ∂P.toMeasure) =
      fderiv ℝ (gradient F) x := by
  letI : NormedSpace ℝ (PiLp 2 E) := inferInstance
  have he : (fun y => ∫ z, dependentConservativeLoss F p V z y ∂P.toMeasure) = F := by
    funext y
    simpa only [PMF.integral_eq_sum, pmfMean] using dependentConservativeLoss_mean P F p V hmean y
  have hs (z : Ω) := dependentConservativeLoss_contDiff F p V hF hp hV z
  refine ⟨congrFun he x, ?_, ?_⟩
  · rw [← gradient_finiteMean P _ x (fun z => (hs z).differentiable (by norm_num) x), he]
  · rw [← fderiv_gradient_finiteMean P _ x hs, he]

end
end SecondOrder

namespace SecondOrder
noncomputable section
variable {n : ℕ} {E : Fin n → Type*} {Ω : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

/-- Value and actual derivative errors of the same conservative loss on
arbitrary disjoint Hilbert blocks. Taking the payload bounds to be twice
the local-noise bounds gives the manuscript's conservative embedding bounds. -/
theorem dependentConservativeLoss_error_bounds
    (F : PiLp 2 E → ℝ) (p : (i : Fin n) → E i → ℝ)
    (V : Ω → ℕ → PiLp 2 E → ℝ) (z : Ω)
    (hF : ContDiff ℝ 2 F) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (hV : ∀ k ≤ n, ContDiff ℝ 2 (V z k)) (x : PiLp 2 E)
    (hp0 : ∀ i, 0 ≤ p i (x i)) (hp1 : ∀ i, p i (x i) ≤ 1)
    (v₀ v₁ v₂ ell h : ℝ) (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    (hell : 0 ≤ ell) (hh : 0 ≤ h)
    (hval : ∀ k ≤ n, |V z k x| ≤ v₀) (hder : ∀ k ≤ n, ‖gradient (V z k) x‖ ≤ v₁)
    (hsecond : ∀ k ≤ n, ‖fderiv ℝ (gradient (V z k)) x‖ ≤ v₂)
    (hfisher : ∀ i, ‖gradient (p i) (x i)‖^2 ≤ ell^2*p i (x i)*(1-p i (x i)))
    (hH : ∀ i, ‖fderiv ℝ (gradient (p i)) (x i)‖ ≤ h) :
    ContDiff ℝ 2 (dependentConservativeLoss F p V z) ∧
      |dependentConservativeLoss F p V z x-F x| ≤ v₀ ∧
      ‖gradient (dependentConservativeLoss F p V z) x-gradient F x‖ ≤ v₁+v₀*ell ∧
      ‖fderiv ℝ (gradient (dependentConservativeLoss F p V z)) x-
        fderiv ℝ (gradient F) x‖ ≤ v₂+2*v₁*ell+2*v₀*(h+ell^2) := by
  have hb := dependentReverseSelector_bounds p (V z) hp hV x hp0 hp1
    v₀ v₁ v₂ ell h hv₀ hv₁ hv₂ hell hh hval hder hsecond hfisher hH
  refine ⟨hF.add hb.1, ?_, ?_, ?_⟩
  · simpa only [dependentConservativeLoss, add_sub_cancel_left] using hb.2.1
  · change ‖gradient (fun y => F y+dependentReverseSelector p (V z) y) x-gradient F x‖ ≤ _
    rw [gradient_add_scalar (hF.differentiable (by norm_num)) (hb.1.differentiable (by norm_num))]
    simpa only [add_sub_cancel_left] using hb.2.2.1
  · change ‖fderiv ℝ (gradient (fun y => F y+dependentReverseSelector p (V z) y)) x-
      fderiv ℝ (gradient F) x‖ ≤ _
    rw [hessian_add_scalar hF hb.1]
    simpa only [add_sub_cancel_left] using hb.2.2.2

end
end SecondOrder
