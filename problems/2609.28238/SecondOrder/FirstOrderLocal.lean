import SecondOrder.FirstOrderJets
import SecondOrder.CurvatureLocal

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderLocalLink (Θ : Fin (T+1) → Fin d → Bool) (i : Fin T)
    (y : LocalBlockSpace (fun _ : Fin (T+1) => Point d) (chainSupport i)) : ℝ :=
  firstOrderBlockCompletion (Θ i.castSucc) (y (chainLeft i))*
    firstOrderBlockPotential (Θ i.succ) (y (chainRight i))

theorem firstOrderLocalLink_contDiff (Θ : Fin (T+1) → Fin d → Bool) (i : Fin T) :
    ContDiff ℝ 3 (firstOrderLocalLink Θ i) :=
  ((firstOrderBlockCompletion_contDiff (Θ i.castSucc)).comp
    (blockProj (E := Point d) (chainLeft i)).contDiff).mul
    ((firstOrderBlockPotential_contDiff (Θ i.succ) 3).comp
      (blockProj (E := Point d) (chainRight i)).contDiff)

theorem firstOrderLocalLink_bounds (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d) (i : Fin T)
    (y : LocalBlockSpace (fun _ : Fin (T+1) => Point d) (chainSupport i)) :
    ‖iteratedFDeriv ℝ 2 (firstOrderLocalLink Θ i) y‖≤4*firstOrderJetConstant^2 ∧
    ‖iteratedFDeriv ℝ 3 (firstOrderLocalLink Θ i) y‖≤8*firstOrderJetConstant^2*Real.sqrt d := by
  let L := blockProj (E := Point d) (chainLeft i)
  let R := blockProj (E := Point d) (chainRight i)
  have hf := (firstOrderBlockCompletion_contDiff (Θ i.castSucc)).comp L.contDiff
  have hg := (firstOrderBlockPotential_contDiff (Θ i.succ) 3).comp R.contDiff
  have hjf := (firstOrderBlockCompletion_jet (Θ i.castSucc) hd (L y)).comp_linear
    (firstOrderBlockCompletion_contDiff (Θ i.castSucc)) L (blockProj_norm_le_one _) y
  have hjg := (firstOrderBlockPotential_jet (Θ i.succ) hd (R y)).comp_linear
    (firstOrderBlockPotential_contDiff (Θ i.succ) 3) R (blockProj_norm_le_one _) y
  have hC : 0≤firstOrderJetConstant := le_trans (by norm_num) firstOrderJetConstant_ge_one
  have hS : 1≤Real.sqrt (d:ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hd)
  exact ⟨scaledThirdJet_product_second hf hg hC y hjf hjg,
    scaledThirdJet_product_third hf hg hC hS y hjf hjg⟩

/-- The public unary regularizers and scaled links form a family with overlap three. -/
def firstOrderLocalTerm (Θ : Fin (T+1) → Fin d → Bool) :
    ∀ i : Sum (Fin (T+1)) (Fin T),
      LocalBlockSpace (fun _ : Fin (T+1) => Point d) (regularizedChainSupport i) → ℝ
  | .inl j => fun y => firstOrderBlockRegularizer (y ⟨j,by simp [regularizedChainSupport]⟩)
  | .inr i => fun y => 2*firstOrderLocalLink Θ i y

theorem firstOrderLocalTerm_contDiff (Θ : Fin (T+1) → Fin d → Bool)
    (i : Sum (Fin (T+1)) (Fin T)) : ContDiff ℝ 3 (firstOrderLocalTerm Θ i) := by
  cases i with
  | inl j =>
    exact (firstOrderBlockRegularizer_contDiff 3).comp
      (blockProj (E := Point d) (⟨j,by simp [regularizedChainSupport]⟩ : regularizedChainSupport (Sum.inl j : Sum (Fin (T+1)) (Fin T)))).contDiff
  | inr i => exact contDiff_const.mul (firstOrderLocalLink_contDiff Θ i)

theorem firstOrderLocalTerm_bounds (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (i : Sum (Fin (T+1)) (Fin T))
    (y : LocalBlockSpace (fun _ : Fin (T+1) => Point d) (regularizedChainSupport i)) :
    ‖iteratedFDeriv ℝ 2 (firstOrderLocalTerm Θ i) y‖≤8*firstOrderJetConstant^2 ∧
    ‖iteratedFDeriv ℝ 3 (firstOrderLocalTerm Θ i) y‖≤16*firstOrderJetConstant^2*Real.sqrt d := by
  have hC : 1≤firstOrderJetConstant^2 := by nlinarith [firstOrderJetConstant_ge_one]
  cases i with
  | inl j =>
    let L := blockProj (E := Point d)
      (⟨j,by simp [regularizedChainSupport]⟩ : regularizedChainSupport (Sum.inl j : Sum (Fin (T+1)) (Fin T)))
    have h2 := iteratedFDeriv_linear_contraction firstOrderBlockRegularizer L (blockProj_norm_le_one _)
      2 (firstOrderBlockRegularizer_contDiff 2) y
    have h3 := iteratedFDeriv_linear_contraction firstOrderBlockRegularizer L (blockProj_norm_le_one _)
      3 (firstOrderBlockRegularizer_contDiff 3) y
    have hr2 : ‖iteratedFDeriv ℝ 2 firstOrderBlockRegularizer (L y)‖≤8 := by
      rw [←norm_fderiv_gradient]
      exact firstOrderBlockRegularizer_hessian_bound hd (L y)
    constructor
    · exact (h2.trans hr2).trans (by nlinarith only [hC])
    · exact (h3.trans (firstOrderBlockRegularizer_third_bound hd (L y))).trans
        (mul_le_mul_of_nonneg_right (by nlinarith only [hC] : 16≤16*firstOrderJetConstant^2) (Real.sqrt_nonneg (d:ℝ)))
  | inr i =>
    have hh := firstOrderLocalLink_bounds Θ hd i y
    have hf := firstOrderLocalLink_contDiff Θ i
    constructor
    · change ‖iteratedFDeriv ℝ 2 (fun z => (2:ℝ) • firstOrderLocalLink Θ i z) y‖≤_
      rw [iteratedFDeriv_const_smul_apply' (hf.of_le (show (2:WithTop ℕ∞)≤3 by decide)).contDiffAt,norm_smul]
      norm_num
      linarith [hh.1]
    · change ‖iteratedFDeriv ℝ 3 (fun z => (2:ℝ) • firstOrderLocalLink Θ i z) y‖≤_
      rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt,norm_smul]
      norm_num
      linarith [hh.2]

theorem firstOrderChain_eq_local (Θ : Fin (T+1) → Fin d → Bool) :
    firstOrderChain Θ=fun x => firstOrderBlockPotential (Θ 0) (x 0)+
      localObjective (fun _ : Fin (T+1) => Point d) regularizedChainSupport (firstOrderLocalTerm Θ) x := by
  funext x
  unfold firstOrderChain localObjective
  rw [Fintype.sum_sum_type]
  change firstOrderBlockPotential (Θ 0) (x 0)+
    (∑ i : Fin T, 2*(firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc)*
      firstOrderBlockPotential (Θ i.succ) (x i.succ)))+
    (∑ j : Fin (T+1), firstOrderBlockRegularizer (x j))=
    firstOrderBlockPotential (Θ 0) (x 0)+
      ((∑ j : Fin (T+1), firstOrderBlockRegularizer (x j))+
      ∑ i : Fin T, 2*(firstOrderBlockCompletion (Θ i.castSucc) (x i.castSucc)*
        firstOrderBlockPotential (Θ i.succ) (x i.succ)))
  abel

end
end SecondOrder
