import Bilevel.CachedOuterProcedure

/-! The fixed public solver radius is valid on every possible outer trace,
including traces after prior failures. No stochastic accuracy event is needed. -/
noncomputable section
namespace Bilevel.CachedOuterProcedure

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

omit [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace Y] [FiniteDimensional ℝ Y] in
theorem current_radius {Λ cap : ℝ} (hΛ : 0 < Λ) (hcap : 0 ≤ cap)
    (x₀ : X) (s : State X Y) (n N : ℕ) (hn : n ≤ N) :
    ‖current Λ cap x₀ n s-x₀‖ ≤ Real.sqrt (N*cap)/Λ := by
  have hh := CappedExecution.all_history_radius hΛ hcap x₀ s.1 n
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hΛ.le
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hcap

theorem current_untilted_initialization {Λ cap R₀ D : ℝ} (hΛ : 0 < Λ) (hcap : 0 ≤ cap)
    (x₀ : X) (yinit : Y) (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀)
    (N : ℕ) (hD : R₀+Lg/μ*(Real.sqrt (N*cap)/Λ) ≤ D)
    (s : State X Y) (n : ℕ) (hn : n ≤ N) :
    ‖yinit-P.canonicalResponse.y (current Λ cap x₀ n s)‖ ≤ D := by
  have hr := P.response_distance_bound P.canonicalResponse (current Λ cap x₀ n s) x₀
  have hm := mul_le_mul_of_nonneg_left (current_radius hΛ hcap x₀ s n N hn)
    (div_nonneg P.Lg_nonneg P.μ_pos.le)
  have hh := norm_sub_le_norm_sub_add_norm_sub yinit (P.canonicalResponse.y x₀)
    (P.canonicalResponse.y (current Λ cap x₀ n s))
  rw [norm_sub_rev (P.canonicalResponse.y x₀)] at hh
  linarith

theorem all_history_initialization {Λ cap R₀ D t : ℝ} (hΛ : 0 < Λ) (hcap : 0 ≤ cap)
    (ht : 0 < t) (x₀ : X) (yinit : Y) (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀)
    (N : ℕ) (hD : R₀+Lg/μ*(Real.sqrt (N*cap)/Λ)+t*Cf/μ ≤ D)
    (s : State X Y) (n : ℕ) (hn : n ≤ N) :
    let p := estimatorInput Cf Λ cap x₀ yinit n s
    ‖p.2.2.2-P.canonicalResponse.y p.1‖ ≤ D ∧
      ‖p.2.2.2-P.tiltedResponse p.1 t p.2.2.1‖ ≤ D := by
  let x := current Λ cap x₀ n s
  let a := Clipping.clip Cf s.2.2.2.2.1
  have h₀ := current_untilted_initialization P hΛ hcap x₀ yinit hinit N
    (le_refl (R₀+Lg/μ*(Real.sqrt (N*cap)/Λ))) s n hn
  have hd := FrozenTilt.solution_displacement P.μ_pos ht (P.lower_strong_monotone x)
    (P.minimizer_stationary x _ (P.canonicalResponse.minimizes x))
    (P.tiltedResponse_stationary x t a) (Clipping.bounded Cf P.Cf_nonneg s.2.2.2.2.1)
  have hh := norm_sub_le_norm_sub_add_norm_sub yinit (P.canonicalResponse.y x) (P.tiltedResponse x t a)
  rw [norm_sub_rev (P.canonicalResponse.y x)] at hh
  have hnon : 0 ≤ t*Cf/μ := div_nonneg (mul_nonneg ht.le P.Cf_nonneg) P.μ_pos.le
  change ‖yinit-P.canonicalResponse.y x‖ ≤ D ∧ ‖yinit-P.tiltedResponse x t a‖ ≤ D
  constructor <;> linarith

end Bilevel.CachedOuterProcedure
