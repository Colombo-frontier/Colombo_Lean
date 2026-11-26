import SampleReuse.SlowScale

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

theorem norm_sum_single_fiber {ι J : Type*} [Fintype ι] [DecidableEq J]
    (a : ι → J) (hinj : Function.Injective a) (w : ι → ℝ) (j : J)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    ‖∑ i, if a i = j then w i else 0‖ ≤ C := by
  by_cases h : ∃ i, a i = j
  · obtain ⟨i, rfl⟩ := h
    simpa only [hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hw i
  · have hn : ∀ i, a i ≠ j := by simpa using h
    simpa only [hn, if_false, Finset.sum_const_zero, norm_zero] using hC

theorem chain_coefficient_bound {d T : ℕ} (Θ : Fin (T+1) → Fin d → Bool)
    (x : FirstOrderSpace d T) (j : Fin (T+1)) :
    ‖firstOrderChainCoefficient Θ x j‖ ≤ 6+20*completionDerivativeBound := by
  have hhead : ‖if (0 : Fin (T+1)) = j then (-2 : ℝ) else 0‖ ≤ 2 := by
    split_ifs <;> norm_num
  have hin := norm_sum_single_fiber (fun i : Fin T => i.succ) (Fin.succ_injective T)
    (fun i => -4*firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc)) j
    (by norm_num : (0:ℝ) ≤ 4) (fun i => by
      rw [norm_mul]
      have hb := firstOrderBlockCompletion_mem (Θ i.castSucc) (x i.castSucc)
      rw [Real.norm_of_nonneg hb.1]
      norm_num only [Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<4)]
      linarith)
  have hout := norm_sum_single_fiber (fun i : Fin T => i.castSucc) (Fin.castSucc_injective T)
    (fun i => 2*firstOrderBlockPotential (Θ i.succ) (x i.succ)*
      deriv firstOrderCompletion (firstOrderBlockEncoding (Θ i.castSucc) (x i.castSucc))) j
    (by norm_num [completionDerivativeBound] : 0 ≤ 20*completionDerivativeBound)
    (fun i => by
      have hw : ‖firstOrderBlockPotential (Θ i.succ) (x i.succ)‖ ≤ 10 := by
        rw [Real.norm_eq_abs]
        have h := firstOrderBlockPotential_range (Θ i.succ) (x i.succ)
        exact abs_le.mpr ⟨h.1, h.2.trans (by norm_num)⟩
      have hd := (firstOrderCompletion_derivative_bounds
        (firstOrderBlockEncoding (Θ i.castSucc) (x i.castSucc))).1
      simp only [norm_mul, Real.norm_ofNat]
      nlinarith [mul_le_mul hw hd (norm_nonneg _)
        (by norm_num : (0:ℝ) ≤ 10)])
  unfold firstOrderChainCoefficient
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add hhead hin)) hout).trans_eq (by ring))

theorem sum_block_norm_le {J E : Type*} [Fintype J] [NormedAddCommGroup E]
    (v : HomogeneousBlocks J E) :
    (∑ j, ‖v j‖) ≤ Real.sqrt (Fintype.card J)*‖v‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : J => (1:ℝ)) (fun j => ‖v j‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  have hv := PiLp.norm_sq_eq_of_L2 (fun _ : J => E) v
  have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card J) : (0:ℝ) ≤ Fintype.card J)
  have hn : 0 ≤ Real.sqrt (Fintype.card J)*‖v‖ := by positivity
  nlinarith [sq_nonneg (Real.sqrt (Fintype.card J)*‖v‖ - ∑ j, ‖v j‖)]

theorem block_operator_bound {J E : Type*} [Fintype J] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : HomogeneousBlocks J E →L[ℝ] ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hK : ∀ j v, ‖K (blockUnit j v)‖ ≤ B*‖v‖) :
    ‖K‖ ≤ B*Real.sqrt (Fintype.card J) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : (∑ j, blockUnit j (v j)) = v := by
    ext j
    change blockProj j (∑ i, blockUnit i (v i)) = v j
    rw [map_sum]
    simp [blockProj_apply, blockUnit_apply]
  calc
    ‖K v‖ = ‖∑ j, K (blockUnit j (v j))‖ := by rw [← map_sum, he]
    _ ≤ ∑ j, ‖K (blockUnit j (v j))‖ := norm_sum_le _ _
    _ ≤ ∑ j, B*‖v j‖ := Finset.sum_le_sum (fun j _ => hK j (v j))
    _ = B*(∑ j, ‖v j‖) := by rw [Finset.mul_sum]
    _ ≤ B*(Real.sqrt (Fintype.card J)*‖v‖) :=
      mul_le_mul_of_nonneg_left (sum_block_norm_le v) hB
    _ = (B*Real.sqrt (Fintype.card J))*‖v‖ := by ring

/-- Global bounded gradient of the genuine population chain; the constant
is independent of dimension and chain length. -/
theorem chain_population_gradient_bound {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) (x : FirstOrderSpace d T) :
    ‖gradient (firstOrderChain Θ) x‖ ≤
      (20+40*completionDerivativeBound)*Real.sqrt (T+1:ℕ) := by
  rw [norm_gradient_eq_fderiv]
  have hB : 0 ≤ 20+40*completionDerivativeBound := by norm_num [completionDerivativeBound]
  apply (block_operator_bound (fderiv ℝ (firstOrderChain Θ) x) hB _).trans_eq
    (by simp)
  intro j v
  rw [firstOrderChain_fderiv_block]
  have hq : ‖fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j) v‖ ≤ 2*‖v‖ :=
    ((fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by
        simpa only [norm_gradient_eq_fderiv] using
          firstOrderBlockEncoding_gradient_bound (Θ j) hd (x j)) (norm_nonneg _))
  have hr : ‖fderiv ℝ firstOrderBlockRegularizer (x j) v‖ ≤ 8*‖v‖ :=
    ((fderiv ℝ firstOrderBlockRegularizer (x j)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by
        simpa only [norm_gradient_eq_fderiv] using
          firstOrderBlockRegularizer_gradient_bound hd (x j)) (norm_nonneg _))
  calc
    _ ≤ ‖firstOrderChainCoefficient Θ x j *
        fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j) v‖ +
        ‖fderiv ℝ firstOrderBlockRegularizer (x j) v‖ := norm_add_le _ _
    _ = ‖firstOrderChainCoefficient Θ x j‖ *
        ‖fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j) v‖ +
        ‖fderiv ℝ firstOrderBlockRegularizer (x j) v‖ := by rw [norm_mul]
    _ ≤ (6+20*completionDerivativeBound)*(2*‖v‖)+8*‖v‖ := by
      exact add_le_add (mul_le_mul (chain_coefficient_bound Θ x j) hq
        (norm_nonneg _) (by norm_num [completionDerivativeBound])) hr
    _ = _ := by ring

theorem slow_population_gradient_bound {d T : ℕ}
    (Θ : Fin (T+1) → Fin d → Bool) (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (x : Point (FirstOrderDimension d T)) :
    ‖gradient (scaledFirstOrderPopulation Θ A (slowDilation d)) x‖ ≤
      A*slowDilation d*(20+40*completionDerivativeBound)*Real.sqrt (T+1:ℕ) := by
  have hβ : 0 ≤ slowDilation d := inv_nonneg.mpr (slowAlpha_pos hd).le
  rw [scaledFirstOrderPopulation_gradient_norm,
    abs_of_nonneg (mul_nonneg hA hβ)]
  exact (mul_le_mul_of_nonneg_left (chain_population_gradient_bound Θ hd _)
    (mul_nonneg hA hβ)).trans_eq (by ring)

end
end SampleReuse
