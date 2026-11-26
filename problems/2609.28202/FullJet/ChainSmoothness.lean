import FullJet.ConcreteLink
import FullJet.TensorBounds
import FullJet.BlockEstimate
import FullJet.Smoothness
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ContDiff BigOperators
open Function

set_option maxHeartbeats 800000

namespace FullJet

/-- `T+1` blocks, with the genuine Euclidean product norm. -/
abbrev BlockSpace (T : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin (T + 1) => E)

section Blocks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

noncomputable def blockProjection (i : Fin (T + 1)) : BlockSpace T E →L[ℝ] E :=
  PiLp.proj 2 (fun _ : Fin (T + 1) => E) i

theorem blockProjection_norm_le (i : Fin (T + 1)) : ‖blockProjection (E := E) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using PiLp.norm_apply_le x i

noncomputable def adjacentProjection (j : Fin T) : BlockSpace T E →L[ℝ] E × E :=
  (blockProjection j.castSucc).prod (blockProjection j.succ)

noncomputable def chainLink (θ s : Fin (T + 1) → E) (ρ : ℝ) (j : Fin T) : BlockSpace T E → ℝ :=
  concreteLink (θ j.castSucc) (s j.succ) ρ ∘ adjacentProjection j

theorem chainLink_contDiff (θ s : Fin (T + 1) → E) (ρ : ℝ) (j : Fin T) :
    ContDiff ℝ ∞ (chainLink θ s ρ j) :=
  (concreteLink_contDiff (θ j.castSucc) (s j.succ) ρ).comp
    (adjacentProjection (E := E) j).contDiff

theorem chainLink_derivative_apply_bound (θ s : Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (hs : ∀ j, ‖s j‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ) (j : Fin T)
    (x : BlockSpace T E) (h : Fin k → BlockSpace T E) :
    |iteratedFDeriv ℝ k (chainLink θ s ρ j) x h| ≤
      (localLinkBound k / ρ) * ∏ l, (‖h l j.castSucc‖ + ‖h l j.succ‖) := by
  unfold chainLink
  rw [(adjacentProjection j).iteratedFDeriv_comp_right (concreteLink_contDiff _ _ _) x (by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))]
  exact concreteLink_derivative_apply_bound _ _ (hθ _) (hs _) ρ hρ hρ1 k _
    (fun l => adjacentProjection j (h l))

end Blocks

theorem adjacent_square_sum_fin_le (T : ℕ) (a : Fin (T + 1) → ℝ)
    (ha : ∑ j, a j ^ 2 ≤ 1) :
    ∑ j : Fin T, (a j.castSucc + a j.succ) ^ 2 ≤ 4 := by
  have hl : ∑ j : Fin T, a j.castSucc ^ 2 ≤ 1 := by
    rw [Fin.sum_univ_castSucc] at ha
    nlinarith [sq_nonneg (a (Fin.last T))]
  have hr : ∑ j : Fin T, a j.succ ^ 2 ≤ 1 := by
    rw [Fin.sum_univ_succ] at ha
    nlinarith [sq_nonneg (a 0)]
  calc
    _ ≤ ∑ j : Fin T, (2 * a j.castSucc ^ 2 + 2 * a j.succ ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [sq_nonneg (a j.castSucc - a j.succ)]
    _ = 2 * (∑ j : Fin T, a j.castSucc ^ 2) + 2 * (∑ j : Fin T, a j.succ ^ 2) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 := by linarith

section Blocks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

theorem sum_chainLink_derivative_bound (θ s : Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (hs : ∀ j, ‖s j‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (k : ℕ) (hk : 2 ≤ k) (x : BlockSpace T E) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ j : Fin T, chainLink θ s ρ j y) x‖ ≤
      (localLinkBound k / ρ) * (2 : ℝ) ^ k := by
  rw [iteratedFDeriv_sum (fun j hj => (chainLink_contDiff θ s ρ j).of_le (by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))]
  simp only [Finset.sum_apply]
  apply multilinear_norm_le_of_unit _ _ (mul_nonneg
    (div_nonneg (localLinkBound_nonneg k) hρ.le) (by positivity))
  intro h hnorm
  have hsquare (l : Fin k) : ∑ j : Fin (T + 1), ‖h l j‖ ^ 2 ≤ 1 := by
    rw [← PiLp.norm_sq_eq_of_L2]
    nlinarith [hnorm l, norm_nonneg (h l)]
  have hproducts : (∑ j : Fin T, ∏ l : Fin k, (‖h l j.castSucc‖ + ‖h l j.succ‖)) ≤ 2 ^ k := by
    obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
    exact sum_products_le_two_pow (Finset.univ : Finset (Fin T)) r
      (fun (l : Fin (r + 2)) (j : Fin T) => ‖h l j.castSucc‖ + ‖h l j.succ‖)
      (fun l j hj => add_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun l => adjacent_square_sum_fin_le T (fun j => ‖h l j‖) (hsquare l))
  calc
    _ = |∑ j : Fin T, iteratedFDeriv ℝ k (chainLink θ s ρ j) x h| := by
      simp only [ContinuousMultilinearMap.sum_apply, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin T, |iteratedFDeriv ℝ k (chainLink θ s ρ j) x h| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin T, (localLinkBound k / ρ) * ∏ l, (‖h l j.castSucc‖ + ‖h l j.succ‖) :=
      Finset.sum_le_sum (fun j hj => chainLink_derivative_apply_bound θ s hθ hs ρ hρ hρ1 k j x h)
    _ = (localLinkBound k / ρ) * (∑ j : Fin T, ∏ l, (‖h l j.castSucc‖ + ‖h l j.succ‖)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hproducts (div_nonneg (localLinkBound_nonneg k) hρ.le)

/-- The precise component chain (the manuscript uses `T+1` in place of our `T`). -/
noncomputable def componentChain (θ s : Fin (T + 1) → E) (ρ lam : ℝ) (x : BlockSpace T E) : ℝ :=
  -(ρ⁻¹ * alignment (s 0) (x 0)) - ∑ j : Fin T, chainLink θ s ρ j x + lam / 2 * ‖x‖ ^ 2

theorem componentChain_contDiff (θ s : Fin (T + 1) → E) (ρ lam : ℝ) :
    ContDiff ℝ ∞ (componentChain θ s ρ lam) :=
  ((contDiff_const.mul ((alignment_contDiff (s 0)).comp
    (blockProjection (E := E) (T := T) 0).contDiff)).neg.sub
    (ContDiff.sum (fun j hj => chainLink_contDiff θ s ρ j))).add
      (contDiff_const.mul (contDiff_norm_sq ℝ))

noncomputable def chainDerivativeBound (k : ℕ) : ℝ :=
  radialDerivativeBound k + localLinkBound k * (2 : ℝ) ^ k

theorem chainDerivativeBound_nonneg (k : ℕ) : 0 ≤ chainDerivativeBound k :=
  add_nonneg (radialDerivativeBound_nonneg k) (mul_nonneg (localLinkBound_nonneg k) (by positivity))

theorem firstRow_derivative_bound (s : Fin (T + 1) → E) (hs : ∀ j, ‖s j‖ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (x : BlockSpace T E) :
    ‖iteratedFDeriv ℝ k (fun y : BlockSpace T E => ρ⁻¹ * alignment (s 0) (y 0)) x‖ ≤
      radialDerivativeBound k / ρ := by
  have ha : ContDiff ℝ k (fun y : BlockSpace T E => alignment (s 0) (y 0)) :=
    ((alignment_contDiff (s 0)).comp (blockProjection (E := E) (T := T) 0).contDiff).of_le (by
      exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  have hb := alignment_projection_derivative_bound (s 0) (hs 0)
    (blockProjection (E := E) (T := T) 0) (blockProjection_norm_le 0) k x
  change ‖iteratedFDeriv ℝ k (fun y : BlockSpace T E => ρ⁻¹ • alignment (s 0) (y 0)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ha.contDiffAt]
  have hn := norm_smul (ρ⁻¹) (iteratedFDeriv ℝ k (fun y : BlockSpace T E => alignment (s 0) (y 0)) x)
  rw [hn, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hρ.le)).trans_eq (by ring)

/-- The actual chain-length- and dimension-independent derivative theorem.
`chainDerivativeBound k` has no block-count, dimension, row, or bias argument. -/
theorem componentChain_derivative_bound (θ s : Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (hs : ∀ j, ‖s j‖ ≤ 1)
    (ρ lam : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (k : ℕ) (hk : 3 ≤ k) (x : BlockSpace T E) :
    ‖iteratedFDeriv ℝ k (componentChain θ s ρ lam) x‖ ≤ chainDerivativeBound k / ρ := by
  let f : BlockSpace T E → ℝ := fun y => ρ⁻¹ * alignment (s 0) (y 0)
  let g : BlockSpace T E → ℝ := fun y => ∑ j : Fin T, chainLink θ s ρ j y
  let q : BlockSpace T E → ℝ := fun y => lam / 2 * ‖y‖ ^ 2
  have hf : ContDiff ℝ k f :=
    contDiff_const.mul (((alignment_contDiff (s 0)).comp
      (blockProjection (E := E) (T := T) 0).contDiff).of_le (by
        exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
  have hg : ContDiff ℝ k g := ContDiff.sum (fun j hj => (chainLink_contDiff θ s ρ j).of_le (by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
  have hq : ContDiff ℝ k q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hqzero : iteratedFDeriv ℝ k q x = 0 :=
    iteratedFDeriv_quadratic_regularizer_eq_zero lam k hk x
  have heq : componentChain θ s ρ lam = -(f + g) + q := by
    funext y
    change -(ρ⁻¹ * alignment (s 0) (y 0)) - (∑ j : Fin T, chainLink θ s ρ j y) + lam / 2 * ‖y‖ ^ 2 =
      -(ρ⁻¹ * alignment (s 0) (y 0) + ∑ j : Fin T, chainLink θ s ρ j y) + lam / 2 * ‖y‖ ^ 2
    ring
  rw [heq, iteratedFDeriv_add_apply (𝕜 := ℝ) (x := x) (i := k)
    (f := -(f + g)) (g := q) (hf.add hg).neg.contDiffAt hq.contDiffAt,
    iteratedFDeriv_neg_apply, iteratedFDeriv_add_apply (𝕜 := ℝ) (x := x) hf.contDiffAt hg.contDiffAt,
    hqzero, add_zero, norm_neg]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖ := norm_add_le _ _
    _ ≤ radialDerivativeBound k / ρ + (localLinkBound k / ρ) * (2 : ℝ) ^ k :=
      add_le_add (firstRow_derivative_bound s hs ρ hρ k x)
        (sum_chainLink_derivative_bound θ s hθ hs ρ hρ hρ1 k (by omega) x)
    _ = chainDerivativeBound k / ρ := by unfold chainDerivativeBound; ring

/-- Corollary `cor:p-smooth` for the concrete chain and every fixed `p ≥ 2`. -/
theorem componentChain_p_smooth (θ s : Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (hs : ∀ j, ‖s j‖ ≤ 1)
    (ρ lam : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ℕ) (hp : 2 ≤ p)
    (x y : BlockSpace T E) :
    ‖iteratedFDeriv ℝ p (componentChain θ s ρ lam) x -
      iteratedFDeriv ℝ p (componentChain θ s ρ lam) y‖ ≤
        (chainDerivativeBound (p + 1) / ρ) * ‖x - y‖ :=
  component_smoothness_of_bound p (componentChain_contDiff θ s ρ lam)
    (chainDerivativeBound (p + 1)) ρ (chainDerivativeBound_nonneg _) hρ
    (fun z => componentChain_derivative_bound θ s hθ hs ρ lam hρ hρ1 (p + 1) (by omega) z) x y

end Blocks

end FullJet
