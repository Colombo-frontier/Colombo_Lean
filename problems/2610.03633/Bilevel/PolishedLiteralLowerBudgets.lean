import Bilevel.PolishedLiteralLowerQuadratic

/-! Full source lower-gradient and Hessian regularity. The variables are
exactly outer (x,v) and lower (u,s), with Euclidean product norms. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ZeroChainSchedule
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

theorem sourceLower_split : P.sourceLower=fun q => lowerBase P.μ P.L q+P.sourcePerturbation q := rfl

theorem sourcePerturbation_contDiff : ContDiff ℝ 3 P.sourcePerturbation := by
  rw [P.sourcePerturbation_eq]
  exact P.data.perturbation_contDiff.comp (fullLowerEmbed (X:=X) (U:=U)).contDiff

theorem sourceLower_contDiff : ContDiff ℝ 3 P.sourceLower := by
  rw [P.sourceLower_split]
  exact (lowerBase_contDiff P.μ P.L).add P.sourcePerturbation_contDiff

theorem sourceLower_jet_bound (q : FullMeanSpace (X:=X) (U:=U)) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k P.sourceLower q‖≤‖iteratedFDeriv ℝ k (lowerBase P.μ P.L) q‖+
      ‖iteratedFDeriv ℝ k P.data.perturbation (fullLowerEmbed q)‖ := by
  rw [P.sourceLower_split]
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  rw [iteratedFDeriv_add_apply' (((lowerBase_contDiff P.μ P.L).of_le hk').contDiffAt)
    ((P.sourcePerturbation_contDiff.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add_left (P.sourcePerturbation_jet_le q k hk) _)

end Parameters

/-- Actual full lower mean budgets from a numerical beta*theta threshold.
The second/third estimates are proved for all four source variables. -/
theorem literal_lower_full_budgets : ∃ τ Rho : ℝ,0<τ ∧ 1≤Rho ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (θ : ℝ),
      1≤θ → 0<P.μ → P.μ≤P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.δ=resolution (1/64) P.β θ → P.w=width (1/64) P.β θ → P.β*θ≤τ →
      (∀ q,‖iteratedFDeriv ℝ 2 P.sourceLower q‖≤3*P.L) ∧
      (∀ q,‖iteratedFDeriv ℝ 3 P.sourceLower q‖≤Rho*P.μ*θ) ∧
      (∀ q q',‖gradient P.sourceLower q-gradient P.sourceLower q'‖≤3*P.L*‖q-q'‖) ∧
      (∀ q q',‖fderiv ℝ (gradient P.sourceLower) q-fderiv ℝ (gradient P.sourceLower) q'‖≤
        Rho*P.μ*θ*‖q-q'‖) := by
  obtain ⟨τ,Rho,hτ,hRho,hsmall⟩ := literal_numerical_smallness_certificate
  refine ⟨τ,Rho,hτ,hRho,?_⟩
  intro X U _ _ _ _ _ _ P θ hθ hμ hμL hβ hR hβb hbR hJ hδ hw hscale
  obtain ⟨hsecond,hthird,_⟩ := hsmall X U P θ hθ hμ (hμ.trans_le hμL) hβ hR hβb hbR hJ hδ hw hscale
  have h2 (q : FullMeanSpace (X:=X) (U:=U)) : ‖iteratedFDeriv ℝ 2 P.sourceLower q‖≤3*P.L := by
    have ht := P.sourceLower_jet_bound q 2 (by norm_num)
    have hb := (lowerBase_jets P.μ P.L hμ.le hμL q).1
    have hp := hsecond (fullLowerEmbed q)
    linarith
  have h3 (q : FullMeanSpace (X:=X) (U:=U)) :
      ‖iteratedFDeriv ℝ 3 P.sourceLower q‖≤Rho*P.μ*θ := by
    have ht := P.sourceLower_jet_bound q 3 (by norm_num)
    rw [(lowerBase_jets P.μ P.L hμ.le hμL q).2,zero_add] at ht
    exact ht.trans (hthird (fullLowerEmbed q))
  exact ⟨h2,h3,GradientJetBounds.gradient_lipschitz P.sourceLower_contDiff (3*P.L) h2,
    GradientJetBounds.hessian_lipschitz P.sourceLower_contDiff (Rho*P.μ*θ) h3⟩

end Bilevel.PolishedLiteral
