import SecondOrder.BalancedSigns

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

theorem balancedSigns_sum_zero {m : ℕ} (w : BalancedSigns m) :
    (∑ i, signValue (w.1 i)) = 0 := by
  obtain ⟨π, rfl⟩ := balancedShuffle_surjective m w
  change (∑ i, signValue (π i).2) = 0
  rw [Equiv.sum_comp π (fun i => signValue i.2)]
  simp [Fintype.sum_prod_type, Fintype.sum_bool, signValue]

theorem pairDifference_sq_sum {m : ℕ} {a : PairIndex m → ℝ}
    (ha : ∀ i, |a i| ≤ 1) (π : Equiv.Perm (PairIndex m)) :
    (∑ i, pairDifference a π i^2) ≤ 4*(m:ℝ) := by
  calc
    _ ≤ ∑ _ : Fin m, (4:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hp := abs_le.mp (ha (π.symm (i,true)))
      have hn := abs_le.mp (ha (π.symm (i,false)))
      have hd : |pairDifference a π i| ≤ 2 := by
        rw [abs_le]
        unfold pairDifference
        constructor <;> linarith [hp.1, hp.2, hn.1, hn.2]
      nlinarith [sq_abs (pairDifference a π i), abs_nonneg (pairDifference a π i)]
    _ = _ := by simp; ring

/-- Averaging the conditional Rademacher estimate over the random
pairing gives the balanced-sign tail, with dimension D=2m. -/
theorem balancedSignSum_hoeffding_real {m : ℕ} {a : PairIndex m → ℝ}
    (ha : ∀ i, |a i| ≤ 1) {t : ℝ} (ht : 0 < t) :
    (balancedSignLaw m).real {w | t ≤ |balancedSignSum a w|} ≤
      2*Real.exp (-t^2/(8*(m:ℝ))) := by
  cases m with
  | zero =>
    rw [balancedSignLaw_real_indicator]
    simp [balancedSignSum, not_le.mpr ht]
  | succ m =>
    rw [balancedSignLaw_real_indicator]
    change uniformMean (fun w : BalancedSigns (m+1) =>
      (if t ≤ |balancedSignSum a w| then (1:ℝ) else 0)) ≤ _
    rw [balancedSignSum_mixture a (fun x => if t ≤ |x| then (1:ℝ) else 0)]
    apply uniformMean_le_const
    intro π
    have hp := rademacherSum_hoeffding_proxy (pairDifference a π)
      (by positivity : (0:ℝ) < 4*((m+1:ℕ):ℝ)) ht (pairDifference_sq_sum ha π)
    have hr := ENNReal.toReal_mono (by finiteness) hp
    have he : (signLaw (m+1)).real {w | t ≤ |rademacherSum (pairDifference a π) w|} =
        uniformMean (fun w => if t ≤ |rademacherSum (pairDifference a π) w| then (1:ℝ) else 0) :=
      uniformMeasure_real_indicator _
    change (signLaw (m+1)).real {w | t ≤ |rademacherSum (pairDifference a π) w|} ≤ _ at hr
    rw [he, ENNReal.toReal_ofReal (by positivity)] at hr
    convert hr using 1 <;> congr 2 <;> ring

theorem balancedSignSum_hoeffding {m : ℕ} {a : PairIndex m → ℝ}
    (ha : ∀ i, |a i| ≤ 1) {t : ℝ} (ht : 0 < t) :
    balancedSignLaw m {w | t ≤ |balancedSignSum a w|} ≤
      ENNReal.ofReal (2*Real.exp (-t^2/(4*(2*m:ℕ)))) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  have hb := balancedSignSum_hoeffding_real ha ht
  convert hb using 1 <;> push_cast <;> ring

end
end SecondOrder
