import RationalUniformStep254

noncomputable section
namespace Paper254

/-- The precision is fixed for every scale before the learner receives data. -/
theorem exists_rational_scale_precision {d n : ℕ} (hd : 0<d)
    (a b : ℕ) (hdim : (d:ℝ)≤(2:ℝ)^a)
    (D G lam : ℝ) (lo : Fin n→ℚ) (hi : ℚ)
    (hlo : ∀ e,0<(lo e:ℝ)) (hgap : ∀ e,(lo e:ℝ)<(hi:ℝ))
    (hhi : (hi:ℝ)≤(2:ℝ)^b) (eps : ℝ) (heps : 0<eps) :
    ∃ cfg : Fin n→RationalHistoryParameters,∃ margin : Fin n→ℝ,
      (∀ e,UniformHistoryGuards d (cfg e) (lo e:ℝ) (hi:ℝ)) ∧
      (∀ e,0≤margin e) ∧
      (∀ e,|(cfg e).lowerThreshold-(lo e:ℝ)|≤margin e) ∧
      (∀ e,|(cfg e).upperThreshold-(hi:ℝ)|≤margin e) ∧
      (∀ e,actualHistoryLocalError d D (lo e:ℝ) (hi:ℝ) G lam (cfg e) (margin e)≤eps) := by
  have hex : ∀ e : Fin n,∃ r : ℕ,((2:ℝ)^r)⁻¹≤(hi:ℝ)-(lo e:ℝ) ∧
      actualHistoryLocalError d D (lo e:ℝ) (hi:ℝ) G lam
        (uniformHistoryParameters a b r r (lo e) hi) (((2:ℝ)^(r+2))⁻¹)≤eps :=
    fun e=>exists_uniform_history_budget d a b D G lam (lo e) hi (hgap e) eps heps
  choose r hsep herr using hex
  refine ⟨fun e=>uniformHistoryParameters a b (r e) (r e) (lo e) hi,
    fun e=>((2:ℝ)^(r e+2))⁻¹,?_,?_,?_,?_,herr⟩
  · exact fun e=>uniformHistoryParameters_guards d a b (r e) (r e) hd hdim
      (lo e) hi (hlo e) hhi (hsep e)
  · intro e; positivity
  · intro e
    dsimp [uniformHistoryParameters]
    push_cast
    rw [add_sub_cancel_left,abs_of_pos (by positivity)]
  · intro e
    dsimp [uniformHistoryParameters]
    push_cast
    rw [sub_sub_cancel_left,abs_neg,abs_of_pos (by positivity)]

end Paper254
#print axioms Paper254.exists_rational_scale_precision
