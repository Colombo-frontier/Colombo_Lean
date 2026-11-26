import Bilevel.ChiCarrierJoint

/-! Joint derivative contraction under arbitrary bounded linear inclusions
and projections, including heterogeneous finite Hilbert products. -/
noncomputable section
namespace Bilevel.ChiCarrier
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_jet_contraction (A : X →L[ℝ] E) (hA : ‖A‖≤1)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : X) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (f ∘ A) x‖≤‖iteratedFDeriv ℝ k f (A x)‖ := by
  rw [A.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg A) hA) (norm_nonneg _)

theorem linear_jet_nonzero (A : X →L[ℝ] E)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : X) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (f ∘ A) x≠0) : iteratedFDeriv ℝ k f (A x)≠0 := by
  intro hz
  apply hn
  rw [A.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk),hz]
  ext v
  rfl

end Bilevel.ChiCarrier
