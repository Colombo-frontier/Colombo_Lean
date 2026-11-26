import SecondOrder.CurvatureAdmissibility

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

theorem secondQuadratic_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x v : E) (c : ℝ) :
    secondQuadratic f x (c • v) = c^2*secondQuadratic f x v := by
  simp only [secondQuadratic_eq, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

variable {m T : ℕ}

theorem scaledCurvaturePopulation_quadratic (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) (x v : Point (CurvatureDimension m T)) :
    secondQuadratic (scaledCurvaturePopulation Θ A β) x v =
      A*β^2*secondQuadratic (curvatureChain Θ) (curvatureDilation m T β x)
        (curvatureCoordinates m T v) := by
  have hf : ContDiff ℝ 2 (curvatureChain Θ) :=
    (curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  unfold scaledCurvaturePopulation scalarLinearScaling
  change secondQuadratic (fun y => A*(curvatureChain Θ ∘ curvatureDilation m T β) y) x v = _
  rw [secondQuadratic_const_mul (hf.comp (curvatureDilation m T β).contDiff)]
  change A*secondQuadratic (curvatureChain Θ ∘ curvatureDilation m T β) x v = _
  rw [secondQuadratic_comp_linear hf, curvatureDilation_apply m T β v, secondQuadratic_smul]
  ring

/-- An unfinished block produces a unit direction of actual negative curvature
after the coordinate isometry and input/output scaling. -/
theorem scaledCurvaturePopulation_negative (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {A β : ℝ} (hA : 0≤A) (x : Point (CurvatureDimension m T))
    (hu : ∃ j, ‖periodicMean ((curvatureDilation m T β x) j) (Θ j)‖≤1/4) :
    ∃ v : Point (CurvatureDimension m T), ‖v‖=1 ∧
      ⟪hessian (scaledCurvaturePopulation Θ A β) x v,v⟫_ℝ ≤
        -(A*β^2/((2*m:ℕ):ℝ))/4 := by
  obtain ⟨w,hw,hq⟩ := curvatureChain_negative Θ hm (curvatureDilation m T β x) hu
  let v := (curvatureCoordinates m T).symm w
  have hv : ‖v‖=1 := by simpa only [v, LinearIsometryEquiv.norm_map] using hw
  have hf : ContDiff ℝ 2 (curvatureChain Θ) :=
    (curvatureChain_contDiff Θ).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  have hg : ContDiff ℝ 2 (scaledCurvaturePopulation Θ A β) :=
    (scaledCurvaturePopulation_contDiff Θ A β).of_le (show (2:WithTop ℕ∞)≤3 by decide)
  refine ⟨v,hv,?_⟩
  change ⟪fderiv ℝ (gradient (scaledCurvaturePopulation Θ A β)) x v,v⟫_ℝ≤_
  rw [←secondQuadratic_eq_inner hg, scaledCurvaturePopulation_quadratic]
  simp only [v, LinearIsometryEquiv.apply_symm_apply]
  rw [secondQuadratic_eq_inner hf]
  have hh := mul_le_mul_of_nonneg_left hq (mul_nonneg hA (sq_nonneg β))
  convert hh using 1 <;> ring

theorem curvatureHardFamily_negative (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {L γ : ℝ} (hL : 0<L) (hγ : 0<γ)
    (x : Point (CurvatureDimension m T))
    (hu : ∃ j, ‖periodicMean ((curvatureDilation m T (curvatureInputScale L γ) x) j) (Θ j)‖≤1/4) :
    ∃ v : Point (CurvatureDimension m T), ‖v‖=1 ∧
      ⟪hessian (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
        (curvatureInputScale L γ)) x v,v⟫_ℝ ≤ -2*γ := by
  have hD : (0:ℝ)<(2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  obtain ⟨v,hv,hq⟩ := scaledCurvaturePopulation_negative Θ hm
    (curvatureOutputScale_pos hD hL hγ).le x hu
  rw [(curvatureScales_identities hD hL hγ).1] at hq
  exact ⟨v,hv,by linarith only [hq]⟩

/-- Stationarity of the scaled ordinary Euclidean objective requires every
hidden block correlation to pass the completion threshold. -/
theorem curvatureHardFamily_sosp_block_completion (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    {x : Point (CurvatureDimension m T)}
    (hx : IsSOSP (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
      (curvatureInputScale L γ)) ε γ x) :
    ∀ j, 1/4<‖periodicMean ((curvatureDilation m T (curvatureInputScale L γ) x) j) (Θ j)‖ := by
  intro j
  by_contra hn
  obtain ⟨v,hv,hq⟩ := curvatureHardFamily_negative Θ hm hL hγ x ⟨j,le_of_not_gt hn⟩
  have hh := hx.2 v
  rw [hv] at hh
  simp only [one_pow, mul_one] at hh
  linarith only [hγ, hq, hh]

theorem curvatureHardFamily_sosp_progress (Θ : Fin (T+1) → BalancedVector m)
    (hm : 0<m) {L γ ε : ℝ} (hL : 0<L) (hγ : 0<γ)
    {x : Point (CurvatureDimension m T)}
    (hx : IsSOSP (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) L γ)
      (curvatureInputScale L γ)) ε γ x) :
    curvatureProgress Θ (curvatureDilation m T (curvatureInputScale L γ) x)=T+1 := by
  have hp := curvatureProgress_le Θ (curvatureDilation m T (curvatureInputScale L γ) x)
  by_contra hn
  let j : Fin (T+1) := ⟨curvatureProgress Θ (curvatureDilation m T (curvatureInputScale L γ) x),by omega⟩
  have hz := curvatureProgress_future_zero Θ (curvatureDilation m T (curvatureInputScale L γ) x)
    j (le_refl _)
  have hsmall := (periodicCompletion_eq_zero_iff (Θ j) _).1 hz
  have hlarge := curvatureHardFamily_sosp_block_completion Θ hm hL hγ hx j
  linarith only [hsmall, hlarge]

end
end SecondOrder
