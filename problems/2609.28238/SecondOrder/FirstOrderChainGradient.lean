import SecondOrder.FirstOrderChain

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

theorem firstOrderBlockPotential_fderiv (θ : Fin d → Bool) (x v : Point d) :
    fderiv ℝ (firstOrderBlockPotential θ) x v = -2*fderiv ℝ (firstOrderBlockEncoding θ) x v := by
  unfold firstOrderBlockPotential
  rw [fderiv_const_mul ((differentiable_const 3).add
    ((firstOrderBlockEncoding_contDiff θ 1).differentiable (by norm_num)) x),fderiv_const_add]
  rfl

theorem firstOrderBlockCompletion_fderiv (θ : Fin d → Bool) (x v : Point d) :
    fderiv ℝ (firstOrderBlockCompletion θ) x v=
      deriv firstOrderCompletion (firstOrderBlockEncoding θ x)*fderiv ℝ (firstOrderBlockEncoding θ) x v := by
  have hh := ((firstOrderCompletion_contDiff.differentiable (by norm_num) _).hasDerivAt).comp_hasFDerivAt x
    ((firstOrderBlockEncoding_contDiff θ 1).differentiable (by norm_num) x).hasFDerivAt
  rw [show firstOrderBlockCompletion θ=firstOrderCompletion ∘ firstOrderBlockEncoding θ from rfl,hh.fderiv]
  rfl

theorem firstOrderChain_fderiv_block (Θ : Fin (T+1) → Fin d → Bool)
    (x : FirstOrderSpace d T) (j : Fin (T+1)) (v : Point d) :
    fderiv ℝ (firstOrderChain Θ) x (blockUnit j v)=
      firstOrderChainCoefficient Θ x j*fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j) v+
        fderiv ℝ firstOrderBlockRegularizer (x j) v := by
  have hW (i : Fin (T+1)) := (firstOrderBlockPotential_contDiff (Θ i) 1).differentiable (by norm_num)
  have hb (i : Fin (T+1)) := (firstOrderBlockCompletion_contDiff (Θ i)).differentiable (by norm_num)
  have hr := (firstOrderBlockRegularizer_contDiff (d := d) 1).differentiable (by norm_num)
  have hhead : Differentiable ℝ (fun y : FirstOrderSpace d T => firstOrderBlockPotential (Θ 0) (y 0)) :=
    (hW 0).comp (blockProj (E := Point d) (0:Fin (T+1))).differentiable
  have hbc (i : Fin T) : Differentiable ℝ (fun y : FirstOrderSpace d T =>
      firstOrderBlockCompletion (Θ i.castSucc) (y i.castSucc)) :=
    (hb _).comp (blockProj (E := Point d) i.castSucc).differentiable
  have hws (i : Fin T) : Differentiable ℝ (fun y : FirstOrderSpace d T =>
      firstOrderBlockPotential (Θ i.succ) (y i.succ)) :=
    (hW _).comp (blockProj (E := Point d) i.succ).differentiable
  have hlink (i : Fin T) := (differentiable_const (2:ℝ)).mul ((hbc i).mul (hws i))
  have hreg (i : Fin (T+1)) : Differentiable ℝ (fun y : FirstOrderSpace d T => firstOrderBlockRegularizer (y i)) :=
    hr.comp (blockProj (E := Point d) i).differentiable
  have hh : fderiv ℝ (fun y : FirstOrderSpace d T => firstOrderBlockPotential (Θ 0) (y 0)) x (blockUnit j v)=
      (if (0:Fin (T+1))=j then -2 else 0)*fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j) v := by
    rw [fderiv_block (hW 0),firstOrderBlockPotential_fderiv]
    split_ifs with he
    · rw [he]
    · simp
  have hl (i : Fin T) : fderiv ℝ (fun y : FirstOrderSpace d T =>
      2*(firstOrderBlockCompletion (Θ i.castSucc) (y i.castSucc)*firstOrderBlockPotential (Θ i.succ) (y i.succ)))
        x (blockUnit j v)=
      ((if i.succ=j then -4*firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc) else 0)+
        (if i.castSucc=j then 2*firstOrderBlockPotential (Θ i.succ) (x i.succ)*
          deriv firstOrderCompletion (firstOrderBlockEncoding (Θ i.castSucc) (x i.castSucc)) else 0))*
            fderiv ℝ (firstOrderBlockEncoding (Θ j)) (x j) v := by
    rw [fderiv_const_mul (((hbc i).mul (hws i)) x),fderiv_mul (hbc i x) (hws i x)]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,smul_eq_mul]
    rw [fderiv_block (hb _),fderiv_block (hW _),firstOrderBlockCompletion_fderiv,firstOrderBlockPotential_fderiv]
    by_cases hi : i.castSucc=j <;> by_cases hj : i.succ=j <;>
      simp only [hi,hj,if_true,if_false] <;> (try rw [hi]) <;> (try rw [hj]) <;> ring
  have hs := Differentiable.sum (fun i (_ : i ∈ Finset.univ) => hlink i)
  have hsr := Differentiable.sum (fun i (_ : i ∈ Finset.univ) => hreg i)
  unfold firstOrderChain
  rw [fderiv_add ((hhead.add hs) x) (hsr x),fderiv_add (hhead x) (hs x),
    fderiv_sum (fun i _ => hlink i x),fderiv_sum (fun i _ => hreg i x)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,hh,hl,fderiv_block hr]
  simp [firstOrderChainCoefficient,add_mul,Finset.sum_mul,Finset.sum_add_distrib]
  ring_nf
  congr 1
  calc
    _ = (if j=j then fderiv ℝ firstOrderBlockRegularizer (x j) v else 0) :=
      Finset.sum_eq_single j (by intro i _ hij; exact if_neg hij)
        (by intro hj; exact False.elim (hj (Finset.mem_univ _)))
    _ = _ := if_pos rfl

/-- Restricting the full derivative to a single block recovers the actual block energy derivative. -/
theorem firstOrderChain_blockEnergy_fderiv (Θ : Fin (T+1) → Fin d → Bool)
    (x : FirstOrderSpace d T) (j : Fin (T+1)) (v : Point d) :
    fderiv ℝ (firstOrderChain Θ) x (blockUnit j v)=
      fderiv ℝ (firstOrderBlockEnergy (Θ j) (firstOrderChainCoefficient Θ x j)) (x j) v := by
  rw [firstOrderChain_fderiv_block]
  have hq := (firstOrderBlockEncoding_contDiff (Θ j) 1).differentiable (by norm_num)
  have hr := (firstOrderBlockRegularizer_contDiff (d := d) 1).differentiable (by norm_num)
  unfold firstOrderBlockEnergy
  rw [fderiv_add (((differentiable_const _).mul hq) _) (hr _),fderiv_const_mul (hq _)]
  rfl

theorem firstOrderChain_block_gradient_le (Θ : Fin (T+1) → Fin d → Bool)
    (x : FirstOrderSpace d T) (j : Fin (T+1)) :
    ‖gradient (firstOrderBlockEnergy (Θ j) (firstOrderChainCoefficient Θ x j)) (x j)‖≤
      ‖gradient (firstOrderChain Θ) x‖ := by
  simp only [norm_gradient_eq_fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [←firstOrderChain_blockEnergy_fderiv]
  simpa only [blockUnit_norm] using (fderiv ℝ (firstOrderChain Θ) x).le_opNorm (blockUnit j v)

theorem firstOrderChain_frontier_gradient_lower (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) (j : Fin (T+1))
    (hj : firstOrderBlockEncoding (Θ j) (x j)≤1/2)
    (hprior : ∀ i : Fin (T+1), i<j → 1/2<firstOrderBlockEncoding (Θ i) (x i)) :
    firstOrderGradientConstant≤‖gradient (firstOrderChain Θ) x‖ :=
  (firstOrderBlockEnergy_gradient_lower (Θ j) (firstOrderChainCoefficient_frontier Θ x j hprior) hd (x j) hj).trans
    (firstOrderChain_block_gradient_le Θ x j)

/-- Any unfinished block forces a fixed positive norm for the gradient of the entire chain. -/
theorem firstOrderChain_gradient_lower (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) (h : ∃ j, firstOrderBlockEncoding (Θ j) (x j)≤1/2) :
    firstOrderGradientConstant≤‖gradient (firstOrderChain Θ) x‖ := by
  let S := Finset.univ.filter (fun j : Fin (T+1) => firstOrderBlockEncoding (Θ j) (x j)≤1/2)
  have hs : S.Nonempty := by
    obtain ⟨j,hj⟩ := h
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let j := S.min' hs
  have hj : firstOrderBlockEncoding (Θ j) (x j)≤1/2 := (Finset.mem_filter.mp (Finset.min'_mem S hs)).2
  apply firstOrderChain_frontier_gradient_lower Θ hd x j hj
  intro i hij
  by_contra hi
  have hi' : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hi⟩
  exact (not_lt_of_ge (Finset.min'_le S i hi')) hij

theorem firstOrderChain_small_gradient_completed (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) (hx : ‖gradient (firstOrderChain Θ) x‖<firstOrderGradientConstant) :
    ∀ j, 1/2<firstOrderBlockEncoding (Θ j) (x j) := by
  intro j
  by_contra hj
  exact (not_lt_of_ge (firstOrderChain_gradient_lower Θ hd x ⟨j,le_of_not_gt hj⟩)) hx

end
end SecondOrder
