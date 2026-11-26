import SampleReuse.RadialGeometry
import SampleReuse.RadialScalarBounds
import GradientHessian.RadialHigherDerivatives

open scoped Topology BigOperators InnerProductSpace

namespace SampleReuse
noncomputable section

def squaredRadiusProfile (f : ℝ → ℝ) (t : ℝ) : ℝ := f (Real.sqrt t)

theorem squaredRadiusProfile_contDiff {f : ℝ → ℝ}
    (hf : ∀ n : ℕ∞, ContDiff ℝ n f) {a c : ℝ} (ha : 0 < a)
    (hflat : ∀ r, r ≤ a → f r = c) (n : ℕ∞) :
    ContDiff ℝ n (squaredRadiusProfile f) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < a^2
  · apply (contDiffAt_const (c := c)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ht] with s hs
    exact hflat _ ((Real.sqrt_lt' ha).mpr hs).le
  · have htp : 0 < t := (sq_pos_of_pos ha).trans_le (le_of_not_gt ht)
    exact (hf n).contDiffAt.comp t (Real.contDiffAt_sqrt htp.ne')

theorem compact_scalar_three_jet {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, k ≤ 3 → ∀ t ∈ Set.Icc (0:ℝ) 16,
      ‖iteratedFDeriv ℝ k f t‖ ≤ C := by
  have hex : ∀ k : Fin 4, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0:ℝ) 16,
      ‖iteratedFDeriv ℝ k.val f t‖ ≤ C := by
    intro k
    have hk : (k.val : WithTop ℕ∞) ≤ 3 := by exact_mod_cast (show k.val ≤ 3 by omega)
    obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv hk).continuousOn
    exact ⟨max 0 C, le_max_left _ _, fun t ht => (hC t ht).trans (le_max_right _ _)⟩
  choose C hC hb using hex
  have hs : 0 ≤ ∑ k : Fin 4, C k := Finset.sum_nonneg (fun k _ => hC k)
  refine ⟨1+∑ k : Fin 4, C k, by linarith, ?_⟩
  intro k hk t ht
  have hk4 : k < 4 := by omega
  have hbnd := hb (⟨k,hk4⟩ : Fin 4) t ht
  have hsingle := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ (⟨k,hk4⟩ : Fin 4))
  exact hbnd.trans (hsingle.trans (by linarith))

theorem cutoff_squared_contDiff (n : ℕ∞) :
    ContDiff ℝ n (squaredRadiusProfile radialCutoff) :=
  squaredRadiusProfile_contDiff radialCutoff_contDiff (by norm_num : (0:ℝ) < 1)
    (fun _ hr => radialCutoff_one hr) n

theorem wall_squared_contDiff (n : ℕ∞) :
    ContDiff ℝ n (squaredRadiusProfile radialWallPrimitive) :=
  squaredRadiusProfile_contDiff radialWallPrimitive_contDiff (by norm_num : (0:ℝ) < 1/2)
    (fun _ hr => radialWallPrimitive_zero hr) n

def cutoffSquaredJetConstant : ℝ := (compact_scalar_three_jet (cutoff_squared_contDiff 3)).choose
def wallSquaredJetConstant : ℝ := (compact_scalar_three_jet (wall_squared_contDiff 3)).choose

theorem cutoffSquaredJetConstant_pos : 0 < cutoffSquaredJetConstant :=
  (compact_scalar_three_jet (cutoff_squared_contDiff 3)).choose_spec.1

theorem wallSquaredJetConstant_pos : 0 < wallSquaredJetConstant :=
  (compact_scalar_three_jet (wall_squared_contDiff 3)).choose_spec.1

def cutoffRadialConstant (k : ℕ) : ℝ := k.factorial*cutoffSquaredJetConstant*32^k
def wallRadialConstant (k : ℕ) : ℝ := k.factorial*wallSquaredJetConstant*32^k

theorem cutoffRadialConstant_pos (k : ℕ) : 0 < cutoffRadialConstant k := by
  have h := cutoffSquaredJetConstant_pos
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  dsimp [cutoffRadialConstant]
  positivity

theorem wallRadialConstant_pos (k : ℕ) : 0 < wallRadialConstant k := by
  have h := wallSquaredJetConstant_pos
  have hf : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  dsimp [wallRadialConstant]
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_squaredProfile_comp_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 (squaredRadiusProfile f)) {C : ℝ}
    (hb : ∀ k, k ≤ 3 → ∀ t ∈ Set.Icc (0:ℝ) 16,
      ‖iteratedFDeriv ℝ k (squaredRadiusProfile f) t‖ ≤ C)
    (k : ℕ) (hk : k ≤ 3) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ k (fun y : E => f ‖y‖) x‖ ≤ k.factorial*C*32^k := by
  have he : (fun y : E => f ‖y‖) =
      squaredRadiusProfile f ∘ (fun y : E => ⟪y,y⟫_ℝ) := by
    funext y
    simp only [squaredRadiusProfile, Function.comp_def, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg y)]
  rw [he]
  apply norm_iteratedFDeriv_comp_le hf
    (show ContDiff ℝ 3 (fun y : E => ⟪y,y⟫_ℝ) from contDiff_id.inner ℝ contDiff_id)
    (by exact_mod_cast hk) x
  · intro j hj
    apply hb j (hj.trans hk)
    rw [real_inner_self_eq_norm_sq]
    exact ⟨sq_nonneg _, by nlinarith [norm_nonneg x]⟩
  · intro j hj _
    exact GradientHessian.RadialHigherDerivatives.norm_iteratedFDeriv_inner_self_le hx j hj

theorem unit_cutoff_derivative_on_ball (k : ℕ) (hk : k ≤ 3) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ k (fun y : E => radialCutoff ‖y‖) x‖ ≤ cutoffRadialConstant k :=
  norm_squaredProfile_comp_bound (cutoff_squared_contDiff 3)
    (compact_scalar_three_jet (cutoff_squared_contDiff 3)).choose_spec.2 k hk hx

theorem unit_wall_derivative_on_ball (k : ℕ) (hk : k ≤ 3) {x : E} (hx : ‖x‖ ≤ 4) :
    ‖iteratedFDeriv ℝ k (fun y : E => radialWallPrimitive ‖y‖) x‖ ≤ wallRadialConstant k :=
  norm_squaredProfile_comp_bound (wall_squared_contDiff 3)
    (compact_scalar_three_jet (wall_squared_contDiff 3)).choose_spec.2 k hk hx

theorem unit_cutoff_derivative_bound (k : ℕ) (hk : k ≤ 3) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y : E => radialCutoff ‖y‖) x‖ ≤ cutoffRadialConstant k := by
  by_cases hx : ‖x‖ ≤ 4
  · exact unit_cutoff_derivative_on_ball k hk hx
  have he : (fun y : E => radialCutoff ‖y‖) =ᶠ[𝓝 x] (fun _ => 0) := by
    have hy : ∀ᶠ y : E in 𝓝 x, 2 < ‖y‖ :=
      continuous_norm.continuousAt.eventually (lt_mem_nhds (by linarith : 2 < ‖x‖))
    exact hy.mono (fun _ hy => radialCutoff_zero hy.le)
  rw [iteratedFDeriv_of_eventuallyEq he k]
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, norm_zero] using (cutoffRadialConstant_pos 0).le
  | succ k =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    exact (cutoffRadialConstant_pos (k+1)).le

end
end SampleReuse
