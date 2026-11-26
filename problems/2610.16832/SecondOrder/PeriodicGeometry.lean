import SecondOrder.PeriodicThird

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

theorem periodicBlockPotential_gradient_bound {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    ‖gradient (periodicBlockPotential θ) x‖ ≤ 1/Real.sqrt ((2*m:ℕ):ℝ) := by
  have hs := periodicBlockPotential_gradient_sq_bound θ x
  have he : (1/Real.sqrt ((2*m:ℕ):ℝ))^2 = ((2*m:ℕ):ℝ)⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_div]
  rw [← he] at hs
  have hn : 0 ≤ 1/Real.sqrt ((2*m:ℕ):ℝ) := by positivity
  nlinarith [norm_nonneg (gradient (periodicBlockPotential θ) x)]

theorem periodicBlockPotential_second_third_bound {m : ℕ} (θ : BalancedVector m)
    (hm : 0 < m) (x : Point (2*m)) :
    ‖hessian (periodicBlockPotential θ) x‖+
      ‖iteratedFDeriv ℝ 3 (periodicBlockPotential θ) x‖ ≤ 10/((2*m:ℕ):ℝ) := by
  have h := add_le_add (periodicBlockPotential_hessian_bound θ x)
    (periodicBlockPotential_third_bound θ hm x)
  convert h using 1 <;> ring

theorem periodicBlockPotential_hessian_holder {m : ℕ} (θ : BalancedVector m) (hm : 0 < m)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (x y : Point (2*m)) :
    ‖hessian (periodicBlockPotential θ) x-hessian (periodicBlockPotential θ) y‖ ≤
      (4/((2*m:ℕ):ℝ))^(1-ν)*(8/((2*m:ℕ):ℝ))^ν*‖x-y‖^ν := by
  have h := holder_of_bounded_lipschitz (hessian (periodicBlockPotential θ))
    (by positivity : (0:ℝ) ≤ 2/((2*m:ℕ):ℝ))
    (by positivity : (0:ℝ) ≤ 8/((2*m:ℕ):ℝ)) hν0 hν1
    (periodicBlockPotential_hessian_bound θ)
    (fun x y => periodicBlockPotential_hessian_lipschitz θ hm y x) x y
  convert h using 1 <;> congr 2 <;> ring

/-- The deterministic conclusions of the manuscript's periodic block lemma,
for its actual balanced hidden vector and scalar potential. -/
theorem periodicBlock_geometry {m : ℕ} (θ : BalancedVector m) (hm : 0 < m) (x : Point (2*m)) :
    ContDiff ℝ 3 (periodicBlockPotential θ) ∧
    |periodicBlockPotential θ x| ≤ 1/2 ∧
    ‖gradient (periodicBlockPotential θ) x‖ ≤ 1/Real.sqrt ((2*m:ℕ):ℝ) ∧
    ‖hessian (periodicBlockPotential θ) x‖+
      ‖iteratedFDeriv ℝ 3 (periodicBlockPotential θ) x‖ ≤ 10/((2*m:ℕ):ℝ) ∧
    (‖periodicMean x θ‖ ≤ 1/4 → ∃ v : Point (2*m), ‖v‖ = 1 ∧
      ⟪hessian (periodicBlockPotential θ) x v,v⟫_ℝ ≤ -1/(4*((2*m:ℕ):ℝ))) :=
  ⟨periodicBlockPotential_contDiff θ 3, periodicPotential_abs_le x θ,
    periodicBlockPotential_gradient_bound θ x,
    periodicBlockPotential_second_third_bound θ hm x,
    fun hsmall => periodicBlockPotential_negative θ x hm hsmall⟩

end
end SecondOrder
