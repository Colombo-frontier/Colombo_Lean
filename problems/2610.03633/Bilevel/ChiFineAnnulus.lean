import Bilevel.ChiFineFlattening

/-! Actual annular localization of every jet through order three, including
cutoff boundaries. The nonzero incoming coordinate is shared across all
resolutions because the actual selector jets are pairwise exclusive. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainFlatteningAnnulus

theorem selected_jet_nonzero_term (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Space n) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (selected n f) z≠0) :
    ∃ i : Fin (n+1),iteratedFDeriv ℝ k (term n f i) z≠0 := by
  by_contra! h
  apply hn
  rw [selected_jet_sum n hf z k hk]
  exact Finset.sum_eq_zero (fun i _ => h i)

theorem negativeDifference_flat {δ' δ : ℝ} (hδ' : 0<δ') (hδ : δ'≤δ)
    (k : ℕ) (hk : k≤3) (t : ℝ) (ht : ¬(δ' < |t| ∧ |t| < 2*δ)) :
    iteratedDeriv k (fun u => -resolutionDifference 1 δ' δ u) t=0 := by
  rw [iteratedDeriv_neg,resolutionDifference_flat 1 hδ' hδ k hk t ht,neg_zero]

theorem difference_term_annulus {δ' δ : ℝ} (hδ' : 0<δ') (hδ : δ'≤δ)
    (n : ℕ) (i : Fin (n+1)) (z : Space n) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (term n (fun t => -resolutionDifference 1 δ' δ t) i) z≠0) :
    δ' < |z i| ∧ |z i| < 2*δ := by
  by_contra h
  exact hn (term_flat_profile n (resolutionDifference_contDiff 1 δ' δ).neg i z k hk
    (fun j hj => negativeDifference_flat hδ' hδ j (by omega) (z i) h))

theorem flattened_difference_annulus {δ' δ : ℝ} (hδ' : 0<δ') (hδ : δ'≤δ)
    (n : ℕ) (z : Space n) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (fun w => flattened n δ' w-flattened n δ w) z≠0) :
    ∃ i : Fin (n+1),δ' < |z i| ∧ |z i| < 2*δ := by
  rw [flattened_difference n δ' δ] at hn
  obtain ⟨i,hi⟩ := selected_jet_nonzero_term n (resolutionDifference_contDiff 1 δ' δ).neg z k hk hn
  exact ⟨i,difference_term_annulus hδ' hδ n i z k hk hi⟩

end Bilevel.ChiFine
