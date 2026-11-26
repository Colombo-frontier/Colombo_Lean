import RationalUniformBudget254

noncomputable section
open Matrix
namespace Paper254

/-- The precision is chosen before the states, gradients and rounds. -/
theorem exists_uniform_rational_step {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (hD : 0≤D) (a b : ℕ) (hdim : (d:ℝ)≤(2:ℝ)^a) (lo hi : ℚ)
    (hlo : 0<(lo:ℝ)) (hgap : (lo:ℝ)<(hi:ℝ)) (hH : (hi:ℝ)≤(2:ℝ)^b)
    (G : ℝ) (hG : 0≤G) (lam : ℚ) (hlam : 0≤(lam:ℝ)) (eps : ℝ) (heps : 0<eps) :
    ∃ r : ℕ,let cfg := uniformHistoryParameters a b r r lo hi
      ∃ guards : UniformHistoryGuards d cfg (lo:ℝ) (hi:ℝ),
      ∀ oracle : RationalProjectionProcedure d,∀ hspec : RationalProjectionSpec W oracle,
      ∀ S : RationalHistoryData d,∀ hS : RationalHistoryInvariant W (lo:ℝ) (hi:ℝ) S,
      ∀ g w : Fin d→ℚ,(∀ i,|(g i:ℝ)|≤G) →
      |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
        ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4 →
      let hnext := rationalHistoryStep_preserves hd W oracle hspec cfg (lo:ℝ) (hi:ℝ) hlo
        (hlo.trans hgap) guards S hS lam g w
      ∀ u : W.carrier,(lam:ℝ)*(coordinateSurrogate (2*(lam:ℝ)) (fun j=>(g j:ℝ))
          (fun j=>(w j:ℝ)) (fun j=>(S.mean j:ℝ))-
        smoothedCoordinateSurrogate (2*(lam:ℝ)) (lo:ℝ) (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ)) u.val)≤
        (S.gaussian hS.covariance_pos).potential (lo:ℝ) u.val-
          ((rationalHistoryStep oracle cfg S lam g w).gaussian hnext.covariance_pos).potential (lo:ℝ) u.val+eps := by
  obtain ⟨r,hr,he⟩ := exists_uniform_history_budget d a b D G (lam:ℝ) lo hi hgap eps heps
  let cfg := uniformHistoryParameters a b r r lo hi
  have hg := uniformHistoryParameters_guards d a b r r hd hdim lo hi hlo hH hr
  refine ⟨r,hg,?_⟩
  intro oracle hspec S hS g w hgrad hsmall
  have hL : |(cfg.lowerThreshold:ℝ)-(lo:ℝ)|≤((2:ℝ)^(r+2))⁻¹ := by
    dsimp [cfg,uniformHistoryParameters]
    push_cast
    rw [add_sub_cancel_left,abs_of_pos (by positivity)]
  have hU : |(cfg.upperThreshold:ℝ)-(hi:ℝ)|≤((2:ℝ)^(r+2))⁻¹ := by
    dsimp [cfg,uniformHistoryParameters]
    push_cast
    rw [sub_sub_cancel_left,abs_neg,abs_of_pos (by positivity)]
  have hs := rationalHistoryStep_one_step hd W hD oracle hspec cfg (lo:ℝ) (hi:ℝ) G
    hlo (hlo.trans hgap) hG hgap.le hg S hS lam hlam g w hgrad hsmall
    (((2:ℝ)^(r+2))⁻¹) (by positivity) hL hU
  dsimp only at hs ⊢
  intro u
  exact (hs u).trans (add_le_add_left he _)

theorem strict_scale_reduction (D T tau : ℝ) (hD : 0<D) (hT : 2≤T)
    (hlo : D/T≤tau) (hhi : tau≤D) :
    D/T≤min tau (D/2) ∧ 0<min tau (D/2) ∧
    min tau (D/2)≤D/2 ∧ tau/2≤min tau (D/2) := by
  have hdiv : D/T≤D/2 := div_le_div_of_nonneg_left hD.le (by norm_num) hT
  have htau : 0<tau := (div_pos hD (by linarith)).trans_le hlo
  exact ⟨le_min hlo hdiv,lt_min htau (by positivity),min_le_right _ _,
    le_min (by linarith) (by linarith)⟩

theorem strict_scale_objective (A B T D tau : ℝ) (hA : 0≤A) (hB : 0≤B) (hT : 0≤T)
    (hD : 0<D) (htau : 0<tau) (hhi : tau≤D) :
    A/(min tau (D/2))+B*T*(min tau (D/2))^2≤2*(A/tau+B*T*tau^2) := by
  have hm : 0<min tau (D/2) := lt_min htau (by positivity)
  have hl : tau/2≤min tau (D/2) := le_min (by linarith) (by linarith)
  have hinv := div_le_div_of_nonneg_left hA (by positivity : 0<tau/2) hl
  have hs := pow_le_pow_left₀ hm.le (min_le_left tau (D/2)) 2
  have hterm := mul_le_mul_of_nonneg_left hs (mul_nonneg hB hT)
  have he : A/(tau/2)=2*(A/tau) := by ring
  rw [he] at hinv
  nlinarith [mul_nonneg (mul_nonneg hB hT) (sq_nonneg tau)]

end Paper254
#print axioms Paper254.exists_uniform_rational_step
