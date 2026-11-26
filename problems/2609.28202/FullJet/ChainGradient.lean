import FullJet.ChainAverage
import FullJet.RadialGradient
import Mathlib.Analysis.Calculus.Deriv.Slope

open scoped ContDiff BigOperators InnerProductSpace Topology
open Filter Set

namespace FullJet

theorem gate_deriv_nonneg (a b t : ℝ) (hab : a < b) : 0 ≤ deriv (gate a b) t := by
  have hd : HasDerivAt (gate a b) (deriv (gate a b) t) t :=
    ((gate_contDiff a b).differentiable (by simp)).differentiableAt.hasDerivAt
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with u hu
  change 0 ≤ u⁻¹ * (gate a b (t + u) - gate a b t)
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt hu))
    (sub_nonneg.mpr (gate_monotone hab (le_add_of_nonneg_right (le_of_lt hu))))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

instance blockSpaceComplete [CompleteSpace E] : CompleteSpace (BlockSpace T E) :=
  inferInstanceAs (CompleteSpace (Fin (T + 1) → E))

noncomputable def blockAlignmentDifferential (θ : Fin (T + 1) → E)
    (x : BlockSpace T E) (j : Fin (T + 1)) : BlockSpace T E →L[ℝ] ℝ :=
  (innerSL ℝ (alignmentGradient (θ j) (x j))).comp (blockProjection j)

theorem blockAlignment_hasFDerivAt (θ : Fin (T + 1) → E)
    (x : BlockSpace T E) (j : Fin (T + 1)) :
    HasFDerivAt (fun y : BlockSpace T E => alignment (θ j) (y j))
      (blockAlignmentDifferential θ x j) x := by
  have h := (alignment_hasFDerivAt (θ j) (x j)).comp x (blockProjection (E := E) j).hasFDerivAt
  exact h

noncomputable def baseChainDifferential (θ : Fin (T + 1) → E) (lam : ℝ)
    (x : BlockSpace T E) : BlockSpace T E →L[ℝ] ℝ :=
  -(blockAlignmentDifferential θ x 0) -
    ∑ j : Fin T, (
      gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) •
        blockAlignmentDifferential θ x j.succ +
      ((alignment (θ j.succ) (x j.succ) + 1) *
        deriv (gate (5 / 32) (9 / 32)) (alignment (θ j.castSucc) (x j.castSucc))) •
          blockAlignmentDifferential θ x j.castSucc) +
    lam • innerSL ℝ x

theorem baseChain_hasFDerivAt (θ : Fin (T + 1) → E) (lam : ℝ) (x : BlockSpace T E) :
    HasFDerivAt (baseChain θ lam) (baseChainDifferential θ lam x) x := by
  have hlink (j : Fin T) :=
    (((gate_contDiff (5 / 32) (9 / 32)).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
      (blockAlignment_hasFDerivAt θ x j.castSucc)).mul
        ((blockAlignment_hasFDerivAt θ x j.succ).add_const 1)
  have hreg : HasFDerivAt (fun y : BlockSpace T E => lam / 2 * ‖y‖ ^ 2) (lam • innerSL ℝ x) x := by
    convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (lam / 2)) using 1
    ext v
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  convert ((blockAlignment_hasFDerivAt θ x 0).neg.sub
    (HasFDerivAt.sum (fun j hj => hlink j))).add hreg using 1
  simp only [baseChainDifferential, smul_smul, Function.comp_apply]

noncomputable def blockVector (j : Fin (T + 1)) (v : E) : BlockSpace T E :=
  (WithLp.equiv 2 (Fin (T + 1) → E)).symm (Pi.single j v)

theorem blockVector_apply (j k : Fin (T + 1)) (v : E) :
    blockVector j v k = if k = j then v else 0 := by
  simp [blockVector, Pi.single_apply, eq_comm]

theorem blockVector_norm (j : Fin (T + 1)) (v : E) : ‖blockVector j v‖ = ‖v‖ :=
  PiLp.norm_equiv_symm_single 2 (fun _ : Fin (T + 1) => E) j v

theorem inner_blockVector (x : BlockSpace T E) (j : Fin (T + 1)) (v : E) :
    ⟪x, blockVector j v⟫_ℝ = ⟪x j, v⟫_ℝ := by
  rw [PiLp.inner_apply]
  simp only [blockVector_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [hkj]
  · simp

theorem blockAlignmentDifferential_blockVector (θ : Fin (T + 1) → E)
    (x : BlockSpace T E) (j k : Fin (T + 1)) (v : E) :
    blockAlignmentDifferential θ x j (blockVector k v) =
      if j = k then ⟪alignmentGradient (θ k) (x k), v⟫_ℝ else 0 := by
  change ⟪alignmentGradient (θ j) (x j), blockVector k v j⟫_ℝ = _
  rw [blockVector_apply]
  split_ifs with h
  · subst j; rfl
  · simp

noncomputable def activeCoefficient (θ : Fin (T + 1) → E) (x : BlockSpace T E)
    (k : Fin (T + 1)) : ℝ :=
  (if k = 0 then 1 else 0) + ∑ j : Fin T,
    ((if j.succ = k then gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) else 0) +
    (if j.castSucc = k then (alignment (θ j.succ) (x j.succ) + 1) *
      deriv (gate (5 / 32) (9 / 32)) (alignment (θ j.castSucc) (x j.castSucc)) else 0))

theorem baseChain_fderiv_blockVector (θ : Fin (T + 1) → E) (lam : ℝ)
    (x : BlockSpace T E) (k : Fin (T + 1)) (v : E) :
    fderiv ℝ (baseChain θ lam) x (blockVector k v) =
      ⟪lam • x k - activeCoefficient θ x k • alignmentGradient (θ k) (x k), v⟫_ℝ := by
  rw [(baseChain_hasFDerivAt θ lam x).fderiv]
  simp only [baseChainDifferential, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply, smul_eq_mul, blockAlignmentDifferential_blockVector, inner_blockVector,
    inner_sub_left, real_inner_smul_left, activeCoefficient,
    add_mul, Finset.sum_mul, ite_mul, mul_ite, zero_mul, mul_zero, one_mul]
  rw [show (if (0 : Fin (T + 1)) = k then ⟪alignmentGradient (θ k) (x k), v⟫_ℝ else 0) =
      (if k = 0 then ⟪alignmentGradient (θ k) (x k), v⟫_ℝ else 0) by simp only [eq_comm]]
  simp only [mul_assoc]
  ring

theorem baseChain_fderiv_norm_ge_block (θ : Fin (T + 1) → E) (lam : ℝ)
    (x : BlockSpace T E) (k : Fin (T + 1)) :
    ‖lam • x k - activeCoefficient θ x k • alignmentGradient (θ k) (x k)‖ ≤
      ‖fderiv ℝ (baseChain θ lam) x‖ := by
  let v := lam • x k - activeCoefficient θ x k • alignmentGradient (θ k) (x k)
  have h := (fderiv ℝ (baseChain θ lam) x).le_opNorm (blockVector k v)
  rw [baseChain_fderiv_blockVector, blockVector_norm] at h
  change ‖⟪v, v⟫_ℝ‖ ≤ ‖fderiv ℝ (baseChain θ lam) x‖ * ‖v‖ at h
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
  change ‖v‖ ≤ _
  by_cases hv : v = 0
  · simpa only [hv, norm_zero] using norm_nonneg (fderiv ℝ (baseChain θ lam) x)
  · have hvpos := norm_pos_iff.mpr hv
    nlinarith

theorem activeCoefficient_ge_one_at_first (θ : Fin (T + 1) → E)
    (hθ : ∀ j, ‖θ j‖ ≤ 1) (x : BlockSpace T E) (k : Fin (T + 1))
    (hprev : ∀ i < k, (9 / 32 : ℝ) ≤ alignment (θ i) (x i)) :
    1 ≤ activeCoefficient θ x k := by
  have hnext (j : Fin T) : 0 ≤ (alignment (θ j.succ) (x j.succ) + 1) *
      deriv (gate (5 / 32) (9 / 32)) (alignment (θ j.castSucc) (x j.castSucc)) := by
    have hq := (abs_le.mp ((alignment_bound (θ j.succ) (x j.succ)).trans (hθ j.succ))).1
    exact mul_nonneg (by linarith) (gate_deriv_nonneg _ _ _ (by norm_num))
  have hterms (j : Fin T) : 0 ≤
      (if j.succ = k then gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) else 0) +
      (if j.castSucc = k then (alignment (θ j.succ) (x j.succ) + 1) *
        deriv (gate (5 / 32) (9 / 32)) (alignment (θ j.castSucc) (x j.castSucc)) else 0) := by
    apply add_nonneg
    · split_ifs <;> first | exact (gate_range _ _ _).1 | exact le_rfl
    · split_ifs <;> first | exact hnext j | exact le_rfl
  unfold activeCoefficient
  cases k using Fin.cases with
  | zero =>
    simp only [if_true]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j hj => hterms j))
  | succ j =>
    simp only [Fin.succ_ne_zero, if_false, zero_add]
    have hjlt : j.castSucc < j.succ := by change j.val < j.val + 1; omega
    have hgate : gate (5 / 32) (9 / 32) (alignment (θ j.castSucc) (x j.castSucc)) = 1 :=
      gate_one (by norm_num) (hprev j.castSucc hjlt)
    have hsingle := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin T))) => hterms i)
      (Finset.mem_univ j)
    simp only [if_true, ne_of_lt hjlt, if_false, add_zero, hgate] at hsingle
    exact hsingle

/-- The deterministic chain gradient barrier from the imported primitives. -/
theorem baseChain_fderiv_lower_bound (θ : Fin (T + 1) → E) (hθ : ∀ j, ‖θ j‖ = 1)
    (x : BlockSpace T E) (hunfinished : ∃ j, alignment (θ j) (x j) < 9 / 32) :
    (1 / 4 : ℝ) ≤ ‖fderiv ℝ (baseChain θ (33 / 16)) x‖ := by
  classical
  let S : Finset (Fin (T + 1)) := Finset.univ.filter (fun j => alignment (θ j) (x j) < 9 / 32)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hunfinished
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let k := S.min' hS
  have hk : alignment (θ k) (x k) < 9 / 32 := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hprev : ∀ i < k, (9 / 32 : ℝ) ≤ alignment (θ i) (x i) := by
    intro i hi
    apply le_of_not_gt
    intro hlt
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩
    exact (not_le_of_gt hi) (S.min'_le i hiS)
  exact (radial_gradient_block_lower_bound (θ k) (x k) (hθ k) (activeCoefficient θ x k)
    (activeCoefficient_ge_one_at_first θ (fun j => (hθ j).le) x k hprev) hk.le).trans
      (baseChain_fderiv_norm_ge_block θ (33 / 16) x k)

/-- The same barrier in the manuscript's gradient notation. -/
theorem baseChain_gradient_lower_bound [CompleteSpace E]
    (θ : Fin (T + 1) → E) (hθ : ∀ j, ‖θ j‖ = 1)
    (x : BlockSpace T E) (hunfinished : ∃ j, alignment (θ j) (x j) < 9 / 32) :
    (1 / 4 : ℝ) ≤ ‖gradient (baseChain θ (33 / 16)) x‖ := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    baseChain_fderiv_lower_bound θ hθ x hunfinished

end FullJet
