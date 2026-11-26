import SampleReuse.RadialProfiles

open scoped Topology BigOperators

namespace SampleReuse
noncomputable section

theorem iteratedFDeriv_of_eventuallyEq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x := by
  simpa only [iteratedFDerivWithin_univ] using
    (h.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq
      (𝕜 := ℝ) (s := Set.univ) h.eq_of_nhds k

theorem norm_iteratedFDeriv_const_le (c : ℝ) (k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun _ : ℝ => c) x‖ ≤ |c| := by
  cases k with
  | zero => simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, le_refl]
  | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; exact abs_nonneg c

/-- Scalar smooth functions with constant tails have uniform derivative bounds.
The compactness used here is one-dimensional, so no ambient dimension enters. -/
theorem plateau_boundedC3 {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b c₀ c₁ : ℝ} (hlo : ∀ x, x ≤ a → f x = c₀)
    (hhi : ∀ x, b ≤ x → f x = c₁) : SecondOrder.BoundedC3 f := by
  have hex : ∀ k : Fin 4, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b,
      ‖iteratedFDeriv ℝ k.val f x‖ ≤ C := by
    intro k
    have hk : (k.val : WithTop ℕ∞) ≤ 3 := by exact_mod_cast (show k.val ≤ 3 by omega)
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv hk).continuousOn
    exact ⟨max 0 C, le_max_left _ _, fun x hx => (hC x hx).trans (le_max_right _ _)⟩
  choose C hC hb using hex
  let D := |c₀|+|c₁|+∑ k : Fin 4, C k
  have hsum : 0 ≤ ∑ k : Fin 4, C k := Finset.sum_nonneg (fun k _ => hC k)
  refine ⟨hf, D, by dsimp [D]; positivity, ?_⟩
  intro x k hk
  have hk4 : k < 4 := by omega
  by_cases hxa : x < a
  · have he : f =ᶠ[𝓝 x] (fun _ => c₀) := by
      filter_upwards [gt_mem_nhds hxa] with y hy
      exact hlo y hy.le
    rw [iteratedFDeriv_of_eventuallyEq he k]
    apply (norm_iteratedFDeriv_const_le c₀ k x).trans
    dsimp [D]
    linarith [abs_nonneg c₁]
  · by_cases hbx : b < x
    · have he : f =ᶠ[𝓝 x] (fun _ => c₁) := by
        filter_upwards [lt_mem_nhds hbx] with y hy
        exact hhi y hy.le
      rw [iteratedFDeriv_of_eventuallyEq he k]
      apply (norm_iteratedFDeriv_const_le c₁ k x).trans
      dsimp [D]
      linarith [abs_nonneg c₀]
    · have hbnd := hb (⟨k,hk4⟩ : Fin 4) x ⟨le_of_not_gt hxa,le_of_not_gt hbx⟩
      have hs := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ (⟨k,hk4⟩ : Fin 4))
      exact hbnd.trans (hs.trans (by dsimp [D]; linarith [abs_nonneg c₀,abs_nonneg c₁]))

theorem radialRise_boundedC3 : SecondOrder.BoundedC3 radialRise :=
  plateau_boundedC3 (radialRise_contDiff 3)
    (fun _ hr => radialRise_zero hr) (fun _ hr => radialRise_one hr)

theorem radialCutoff_boundedC3 : SecondOrder.BoundedC3 radialCutoff :=
  plateau_boundedC3 (radialCutoff_contDiff 3)
    (fun _ hr => radialCutoff_one hr) (fun _ hr => radialCutoff_zero hr)

def radialProfileConstant : ℝ :=
  1+radialRise_boundedC3.2.choose+radialCutoff_boundedC3.2.choose

theorem radialProfileConstant_ge_one : 1 ≤ radialProfileConstant := by
  have hS := radialRise_boundedC3.2.choose_spec.1
  have hχ := radialCutoff_boundedC3.2.choose_spec.1
  dsimp [radialProfileConstant]
  linarith

theorem radialRise_iterated_bound (x : ℝ) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k radialRise x‖ ≤ radialProfileConstant := by
  apply (radialRise_boundedC3.2.choose_spec.2 x k hk).trans
  have hχ := radialCutoff_boundedC3.2.choose_spec.1
  dsimp [radialProfileConstant]
  linarith

theorem radialCutoff_iterated_bound (x : ℝ) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k radialCutoff x‖ ≤ radialProfileConstant := by
  apply (radialCutoff_boundedC3.2.choose_spec.2 x k hk).trans
  have hS := radialRise_boundedC3.2.choose_spec.1
  dsimp [radialProfileConstant]
  linarith

end
end SampleReuse
