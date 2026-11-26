import SecondOrder.ComparisonHiddenConditioning

open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section
variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem finitePiPMF_update_balance (p : ι → PMF α) (i : ι) (w : ι → α) (a : α) :
    (finitePiPMF p w).toReal*(p i a).toReal=
      (finitePiPMF p (Function.update w i a)).toReal*(p i (w i)).toReal := by
  rw [finitePiPMF_toReal, finitePiPMF_toReal,
    ←Finset.mul_prod_erase Finset.univ (fun j => (p j (w j)).toReal) (Finset.mem_univ i),
    ←Finset.mul_prod_erase Finset.univ (fun j => (p j (Function.update w i a j)).toReal) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, (p j (Function.update w i a j)).toReal)=
      ∏ j ∈ Finset.univ.erase i, (p j (w j)).toReal := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he, Function.update_self]
  ring

/-- Replacing one coordinate by a fresh draw from its own law preserves the
whole product law. This applies to arbitrary functions of all coordinates. -/
theorem finitePiPMF_resample_mean (p : ι → PMF α) (i : ι) (F : (ι → α) → ℝ) :
    pmfMean (finitePiPMF p) (fun w => pmfMean (p i) (fun a => F (Function.update w i a)))=
      pmfMean (finitePiPMF p) F := by
  let swap : ((ι → α) × α) → ((ι → α) × α) := fun w => (Function.update w.1 i w.2,w.1 i)
  have hs : Function.Involutive swap := by
    intro w
    apply Prod.ext
    · funext j
      dsimp only [swap]
      by_cases hj : j=i
      · subst j; simp
      · simp only [Function.update_of_ne hj]
    · simp only [swap, Function.update_self]
  have hsum := Fintype.sum_equiv (Equiv.mk swap swap hs hs)
    (fun w : (ι → α) × α => (finitePiPMF p w.1).toReal*(p i w.2).toReal*F (Function.update w.1 i w.2))
    (fun w : (ι → α) × α => (finitePiPMF p w.1).toReal*(p i w.2).toReal*F w.1)
    (fun w => by
      change _=(finitePiPMF p (Function.update w.1 i w.2)).toReal*(p i (w.1 i)).toReal*F (Function.update w.1 i w.2)
      dsimp only
      rw [finitePiPMF_update_balance p i w.1 w.2])
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at hsum
  have hr : (∑ w, ∑ a, (finitePiPMF p w).toReal*(p i a).toReal*F w)=pmfMean (finitePiPMF p) F := by
    simp only [pmfMean, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro w _
    calc
      _ = (finitePiPMF p w).toReal*F w*(∑ a, (p i a).toReal) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [pmf_toReal_sum, mul_one]
  rw [hr] at hsum
  simpa only [pmfMean, smul_eq_mul, Finset.mul_sum, mul_assoc] using hsum

theorem finitePiPMF_resample_mean_any_fintype (I : Fintype (ι → α))
    (p : ι → PMF α) (i : ι) (F : (ι → α) → ℝ) :
    @pmfMean (ι → α) ℝ I _ _ (finitePiPMF p)
      (fun w => pmfMean (p i) (fun a => F (Function.update w i a)))=
      @pmfMean (ι → α) ℝ I _ _ (finitePiPMF p) F := by
  have he : I=@Pi.instFintype ι (fun _ => α) inferInstance inferInstance (fun _ => inferInstance) :=
    Subsingleton.elim _ _
  rw [he]
  exact finitePiPMF_resample_mean p i F

end
end SecondOrder
