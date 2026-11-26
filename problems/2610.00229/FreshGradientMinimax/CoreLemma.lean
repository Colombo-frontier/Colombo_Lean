import FreshGradientMinimax.CoreSeedBounds

/-! Lemma C.1 for the original square links, chain, and seed. All first and
second derivatives in this statement are Lean's actual derivative operators. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

def CoreLinkDerivativeBounds (f : ℝ → ℝ → ℝ) : Prop := ∀ a b : ℝ,
    |f a b| ≤ 4 ∧
    |deriv (fun x => f x b) a| ≤ 20 ∧ |deriv (f a) b| ≤ 20 ∧
    |deriv (deriv (fun x => f x b)) a| ≤ 1000 ∧
    |deriv (fun y => deriv (fun x => f x y) a) b| ≤ 1000 ∧
    |deriv (fun x => deriv (f x) b) a| ≤ 1000 ∧
    |deriv (deriv (f a)) b| ≤ 1000

theorem rootLink_deriv_first (s a b : ℝ) :
    deriv (fun x => rootLink s x b) a = rootLinkD1 s a b :=
  (rootLink_hasDerivAt_first s a b).deriv

theorem rootLink_deriv_second (s a b : ℝ) :
    deriv (rootLink s a) b = rootLinkD2 s a b :=
  (rootLink_hasDerivAt_second s a b).deriv

theorem rootLink_deriv_first_first (s a b : ℝ) :
    deriv (deriv (fun x => rootLink s x b)) a = rootLinkD11 s a b := by
  rw [show deriv (fun x => rootLink s x b) = (fun x => rootLinkD1 s x b) from
    funext (fun x => rootLink_deriv_first s x b)]
  exact (rootLinkD1_hasDerivAt_first s a b).deriv

theorem rootLink_deriv_first_second (s a b : ℝ) :
    deriv (fun y => deriv (fun x => rootLink s x y) a) b = rootLinkD12 s a b := by
  simp_rw [rootLink_deriv_first]
  exact (rootLinkD1_hasDerivAt_second s a b).deriv

theorem rootLink_deriv_second_second (s a b : ℝ) :
    deriv (deriv (rootLink s a)) b = rootLinkD22 s a b := by
  rw [show deriv (rootLink s a) = rootLinkD2 s a from funext (rootLink_deriv_second s a)]
  exact (rootLinkD2_hasDerivAt_second s a b).deriv

theorem rootLink_deriv_second_first (s a b : ℝ) :
    deriv (fun x => deriv (rootLink s x) b) a = rootLinkD12 s a b := by
  simp_rw [rootLink_deriv_second]
  exact (rootLinkD2_hasDerivAt_first s a b).deriv

theorem rootLink_actual_derivative_bounds {s : ℝ} (hs : |s| = 1) :
    CoreLinkDerivativeBounds (rootLink s) := by
  intro a b
  obtain ⟨h0, h1, h2, h11, h12, h22⟩ := rootLink_component_bounds hs a b
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [rootLink_deriv_first]
  · rwa [rootLink_deriv_second]
  · rwa [rootLink_deriv_first_first]
  · rwa [rootLink_deriv_first_second]
  · rwa [rootLink_deriv_second_first]
  · rwa [rootLink_deriv_second_second]

theorem coreLinkPlus_actual_derivative_bounds : CoreLinkDerivativeBounds coreLinkPlus := by
  have he : coreLinkPlus = rootLink (-1) := funext (fun a => funext (coreLinkPlus_rootLink a))
  rw [he]
  exact rootLink_actual_derivative_bounds (by norm_num)

theorem coreLinkMinus_actual_derivative_bounds : CoreLinkDerivativeBounds coreLinkMinus := by
  have he : coreLinkMinus = rootLink 1 := funext (fun a => funext (coreLinkMinus_rootLink a))
  rw [he]
  exact rootLink_actual_derivative_bounds (by norm_num)

theorem lemma_C1 (n : ℕ) :
    ContDiff ℝ 2 (fun z : ℝ × ℝ => coreLinkPlus z.1 z.2) ∧
    ContDiff ℝ 2 (fun z : ℝ × ℝ => coreLinkMinus z.1 z.2) ∧
    CoreLinkDerivativeBounds coreLinkPlus ∧ CoreLinkDerivativeBounds coreLinkMinus ∧
    ContDiff ℝ 2 (@coreChain n) ∧ ContDiff ℝ 2 (@coreSeed n) ∧
    (∀ u : Euclid (n + 1),
      |coreChain u| ≤ 9 * (n + 1 : ℝ) ∧
      ‖gradient coreChain u‖ ≤ 10 ^ 6 * Real.sqrt (n + 1 : ℝ) ∧
      ‖fderiv ℝ (gradient (@coreChain n)) u‖ ≤ 10 ^ 6 ∧
      ‖gradient coreSeed u‖ ≤ 49 * Real.sqrt (n + 1 : ℝ) ∧
      ‖fderiv ℝ (gradient (@coreSeed n)) u‖ ≤ 1537 ∧
      (|u (Fin.last n)| ≤ 1 / 4 →
        ∃ j : Fin (n + 1), |u j| ≤ 1 ∧ gradient coreChain u j ≤ -Real.exp (-(1 / 2 : ℝ)))) := by
  refine ⟨coreLinkPlus_contDiff, coreLinkMinus_contDiff, coreLinkPlus_actual_derivative_bounds,
    coreLinkMinus_actual_derivative_bounds, coreChain_contDiff, coreSeed_contDiff, ?_⟩
  intro u
  exact ⟨squareLinkCore_bound (fun i => u i), coreChain_gradient_original_bound u,
    coreChain_hessian_bound u, coreSeed_gradient_norm u, coreSeed_hessian_bound u,
    coreChain_coordinate_barrier u⟩

end FreshGradientMinimax
