import Bilevel.ChiBoundedChainMasks

/-! Uniform scalar bounds for the concrete bounded activation, including the
square-root derivative estimate required by the revised manuscript. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

theorem deriv_compact_of_two_plateaux {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (c₀ c₁ : ℝ) (h₀ : ∀ t,t≤0 → f t=c₀) (h₁ : ∀ t,1≤t → f t=c₁) :
    HasCompactSupport (deriv f) := by
  apply SmallGapProfileBounds.compactSupport_of_tail 1
  intro t ht
  rcases le_total 0 t with hp|hn
  · apply ZeroChainResidualCutoffs.deriv_zero_of_constant_on (hf t)
      (uniqueDiffOn_Ici 1) (fun x hx => h₁ x hx)
    simpa only [abs_of_nonneg hp] using ht
  · exact ZeroChainResidualCutoffs.deriv_zero_of_constant_on (hf t)
      (uniqueDiffOn_Iic 0) (fun x hx => h₀ x hx) hn

theorem theta_deriv_compactSupport : HasCompactSupport (deriv theta) :=
  deriv_compact_of_two_plateaux ((theta_contDiff (k:=1)).differentiable (by norm_num))
    0 1 (fun _ ht => theta_zero (by linarith)) (fun _ ht => theta_one ht)

theorem psi_deriv_compactSupport : HasCompactSupport (deriv psi) :=
  deriv_compact_of_two_plateaux ((psi_contDiff (k:=1)).differentiable (by norm_num))
    0 1 (fun _ ht => psi_zero (by linarith)) (fun _ ht => psi_one ht)

theorem psi_jet_bound (j : ℕ) (hj : j≤3) :
    ∃ C : ℝ,0≤C ∧ ∀ t,|iteratedDeriv j psi t|≤C :=
  ZeroChainResidualCutoffs.plateau_profile_bound psi psi_contDiff psi_range
    psi_deriv_compactSupport j hj

theorem squared_profile_sqrt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h₀ : ∀ t,0≤f t) (B : ℝ) (hb : ∀ t,|deriv f t|≤B) (t : ℝ) :
    |deriv (fun s => (f s)^2) t|≤(2*B)*Real.sqrt ((f t)^2) := by
  rw [((hf t).hasDerivAt.pow 2).deriv]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one] 
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
    abs_of_nonneg (h₀ t),Real.sqrt_sq (h₀ t)]
  nlinarith [mul_le_mul_of_nonneg_left (hb t) (h₀ t)]

theorem psi_sqrt_derivative : ∃ C : ℝ,0≤C ∧ ∀ t,|deriv psi t|≤C*Real.sqrt (psi t) := by
  obtain ⟨B,hB,hb⟩ := SmallGapProfileBounds.bound_of_compactSupport theta_deriv_compactSupport
    ((theta_contDiff (k:=2)).continuous_deriv (by norm_num))
  refine ⟨2*B,by positivity,fun t => ?_⟩
  exact squared_profile_sqrt_deriv ((theta_contDiff (k:=1)).differentiable (by norm_num))
    (fun s => (theta_range s).1) B hb t

def energyRoot (s : ℝ) : ℝ := 1-Real.smoothTransition ((4*s-1)/3)

theorem energyRoot_contDiff {k : ℕ∞} : ContDiff ℝ k energyRoot :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 3))

theorem energyRoot_nonneg (s : ℝ) : 0≤energyRoot s :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem energyRoot_deriv_compactSupport : HasCompactSupport (deriv energyRoot) := by
  apply deriv_compact_of_two_plateaux ((energyRoot_contDiff (k:=1)).differentiable (by norm_num)) 1 0
  · intro t ht
    simp [energyRoot,Real.smoothTransition.zero_of_nonpos (by linarith : (4*t-1)/3≤0)]
  · intro t ht
    simp [energyRoot,Real.smoothTransition.one_of_one_le (by linarith : 1≤(4*t-1)/3)]

theorem energyCutoff_sqrt_derivative :
    ∃ C : ℝ,0≤C ∧ ∀ t,|deriv energyCutoff t|≤C*Real.sqrt (energyCutoff t) := by
  obtain ⟨B,hB,hb⟩ := SmallGapProfileBounds.bound_of_compactSupport energyRoot_deriv_compactSupport
    ((energyRoot_contDiff (k:=2)).continuous_deriv (by norm_num))
  refine ⟨2*B,by positivity,fun t => ?_⟩
  exact squared_profile_sqrt_deriv ((energyRoot_contDiff (k:=1)).differentiable (by norm_num))
    energyRoot_nonneg B hb t

end Bilevel.ChiBoundedChain
