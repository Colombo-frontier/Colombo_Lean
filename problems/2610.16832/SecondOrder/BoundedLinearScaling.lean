import SecondOrder.ScalarLinearScaling
import SecondOrder.BoundedC3

namespace SecondOrder
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BoundedC3.comp_linear {f : F → ℝ} (hf : BoundedC3 f) (L : E →L[ℝ] F) :
    BoundedC3 (f ∘ L) := by
  obtain ⟨hs,C,hC,hb⟩ := hf
  refine ⟨hs.comp L.contDiff, C*(1+‖L‖)^3, by positivity, ?_⟩
  intro x k hk
  have hp : ‖L‖^k ≤ (1+‖L‖)^3 :=
    (pow_le_pow_left₀ (norm_nonneg L) (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg L]) hk)
  exact (iteratedFDeriv_linear_bound f L k (hs.of_le (by exact_mod_cast hk)) x).trans
    (mul_le_mul (hb (L x) k hk) hp (pow_nonneg (norm_nonneg L) k) hC)

theorem BoundedC3.scalarLinearScaling {f : F → ℝ} (hf : BoundedC3 f)
    (A : ℝ) (L : E →L[ℝ] F) : BoundedC3 (scalarLinearScaling f A L) :=
  (hf.comp_linear L).const_mul A

end
end SecondOrder
