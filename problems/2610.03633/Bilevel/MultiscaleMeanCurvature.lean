import Bilevel.MultiscaleMeanCertificate

/-! Actual hyperobjective curvature for the macro-free inner-carrier
family. The numerical constant is independent of the chain length,
variation parameter, dimension and gap. This is an analytic certificate;
no information lower bound or prescribed-budget normalization is assumed. -/
noncomputable section
namespace Bilevel.MultiscaleMean
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem actual_outer_curvature : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E:=E) n),P.β*Real.sqrt (n+1:ℕ)≤P.R → P.ν≤P.L →
      ∀ u v,‖gradient P.outer u-gradient P.outer v‖≤(C*P.L)*‖u-v‖ := by
  obtain ⟨A,hA,hrevealed⟩ := actual_upper_smoothness
  obtain ⟨B,hB,hresidual⟩ := residual_jet_budget
  refine ⟨A+B,by linarith,?_⟩
  intro E _ _ _ n P hR hν u v
  have hb (x : E) : ‖iteratedFDeriv ℝ 2 P.residual x‖≤B*P.L := by
    have hh := hresidual E n P x 2
    change ‖iteratedFDeriv ℝ 2 P.residual x‖≤B*P.L*P.β^2/P.β^2 at hh
    have he : B*P.L*P.β^2/P.β^2=B*P.L := by field_simp [P.β_pos.ne']
    rwa [he] at hh
  have hr := GradientJetBounds.gradient_lipschitz P.residual_contDiff (B*P.L) hb u v
  have ha := hrevealed E n P hR hν u v
  rw [P.revealed_gradient,P.revealed_gradient] at ha
  have he : gradient P.outer u-gradient P.outer v=
      (gradient P.outer u-gradient P.residual u-(gradient P.outer v-gradient P.residual v))+
        (gradient P.residual u-gradient P.residual v) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ha hr).trans_eq (by ring))

theorem actual_realized_curvature : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E:=E) n),P.β*Real.sqrt (n+1:ℕ)≤P.R → P.ν≤P.L →
      ∀ x z,‖gradient P.realized x-gradient P.realized z‖≤
        (C*P.L*(P.L/P.μ)^2)*‖x-z‖ := by
  obtain ⟨C,hC,houter⟩ := actual_outer_curvature
  refine ⟨C,hC,?_⟩
  intro E _ _ _ n P hR hν x z
  rw [(P.realized_hasGradientAt x).gradient,(P.realized_hasGradientAt z).gradient,
    ←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos P.L_pos P.μ_pos)]
  have hh := houter E n P hR hν ((P.L/P.μ) • x) ((P.L/P.μ) • z)
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos P.L_pos P.μ_pos)] at hh
  exact (mul_le_mul_of_nonneg_left hh (div_pos P.L_pos P.μ_pos).le).trans_eq (by ring)

theorem actual_primitive_curvature : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E:=E) n) (Lf Cf ρ : ℝ) (Q : Realization P Lf Cf ρ),
      P.β*Real.sqrt (n+1:ℕ)≤P.R → P.ν≤P.L →
      ∀ x z,‖gradient (Q.primitive.hyperobjective Q.response) x-gradient (Q.primitive.hyperobjective Q.response) z‖≤
        (C*P.L*(P.L/P.μ)^2)*‖x-z‖ := by
  obtain ⟨C,hC,hmean⟩ := actual_realized_curvature
  refine ⟨C,hC,?_⟩
  intro E _ _ _ n P Lf Cf ρ Q hR hν x z
  rw [Q.objective_eq]
  exact hmean E n P hR hν x z

end Bilevel.MultiscaleMean
