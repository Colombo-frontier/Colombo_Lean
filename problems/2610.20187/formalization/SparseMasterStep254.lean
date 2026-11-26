import SparseMaster254

noncomputable section
open scoped BigOperators
namespace Paper254

def SparseMasterState.expertPrediction {d T K : ℕ} {D : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (e : HistoryExpert T K) : W.carrier :=
  ⟨WithLp.toLp 2 (S.histories e).mean, S.feasible e⟩

def SparseMasterState.rawWeights {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (f : Loss d) : ProbabilityWeights (HistoryExpert T K) :=
  S.weights.exponential (curvature D G η/2)
    (fun e => coordinateSurrogate (curvature D G η)
      (selectedGradient W G f S.prediction) S.prediction.val (S.histories e).mean)

theorem SparseMasterState.step_histories {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (t : Fin T) (f : Loss d)
    (e : HistoryExpert T K) :
    (S.step hD hG hη q hq t f).histories e =
      if e ∈ liveExperts T K (t.val+1) then
        (S.histories e).historyUpdate W (curvature D G η/2) (q e.2)
          (le_of_lt (div_pos (curvature_pos D G η hD hG hη) (by norm_num))) (hq e.2)
          (selectedGradient W G f S.prediction) S.prediction.val else S.histories e := by
  classical
  rfl

theorem SparseMasterState.step_survival {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (t : Fin T) (f : Loss d)
    (e : HistoryExpert T K) (he : e ∈ liveExperts T K (t.val+2)) :
    (1-1/(t.val+2 : ℝ))*(S.rawWeights (G := G) (η := η) f).weight e ≤
      (S.step hD hG hη q hq t f).weights.weight e := by
  have ha : 0 < 1/(t.val+2 : ℝ) := by positivity
  have hb : 1/(t.val+2 : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg t.val (α := ℝ)]
  let fresh : Fin (T+1) := ⟨t.val+1, by omega⟩
  exact ProbabilityWeights.pruneShare_survival (S.rawWeights (G := G) (η := η) f)
    (birthPrior T K fresh) _ ha hb (liveExperts T K (t.val+2))
    (fun j hj => birthPrior_live fresh j hj) e he

theorem SparseMasterState.step_birth {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (t : Fin T) (f : Loss d) (k : Fin (K+1)) :
    (1/(t.val+2 : ℝ))*(1/(K+1 : ℝ)) ≤
      (S.step hD hG hη q hq t f).weights.weight (⟨t.val+1, by omega⟩, k) := by
  classical
  have ha : 0 < 1/(t.val+2 : ℝ) := by positivity
  have hb : 1/(t.val+2 : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg t.val (α := ℝ)]
  let fresh : Fin (T+1) := ⟨t.val+1, by omega⟩
  have he : (fresh,k) ∈ liveExperts T K (t.val+2) :=
    (mem_liveExperts _).mpr (historyActive_birth _ (by omega))
  have hh := ProbabilityWeights.pruneShare_birth (S.rawWeights (G := G) (η := η) f)
    (birthPrior T K fresh) _ ha hb (liveExperts T K (t.val+2))
    (fun j hj => birthPrior_live fresh j hj) (fresh,k) he
  have hp : (birthPrior T K fresh).weight (fresh,k) = 1/(K+1 : ℝ) := by simp [birthPrior]
  rw [hp] at hh
  exact hh

theorem coordinate_surrogate_toLp {d : ℕ} (γ : ℝ) (g w : Space d) (x : Coordinates d) :
    coordinateSurrogate γ g w x = rankOneSurrogate γ g w (WithLp.toLp 2 x) :=
  coordinate_surrogate_eq γ g w (WithLp.toLp 2 x)

theorem SparseMasterState.exponential_comparison {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η)
    (f : Loss d) (hf : AdmissibleLoss W G η f) (e : HistoryExpert T K)
    (he : 0 < S.weights.weight e) :
    let s := rankOneSurrogate (curvature D G η) (selectedGradient W G f S.prediction) S.prediction.val
    (curvature D G η/2)*(s S.prediction.val-s (S.expertPrediction e).val) ≤
      Real.log ((S.rawWeights (G := G) (η := η) f).weight e)-Real.log (S.weights.weight e) := by
  let g := selectedGradient W G f S.prediction
  let s := rankOneSurrogate (curvature D G η) g S.prediction.val
  have hg := (selectedGradient_spec W hf S.prediction).2
  have hconc := surrogate_expConcave W hD hG hη hg S.prediction.property
  have hh := exponential_update_one_step S.weights.weight S.expertPrediction
    S.weights.nonneg S.weights.total hconc e he
  change (curvature D G η/2)*(s S.prediction.val-s (S.expertPrediction e).val) ≤ _
  change _ ≤ Real.log (exponentialUpdate (curvature D G η/2) S.weights.weight
    (fun j => coordinateSurrogate (curvature D G η) g S.prediction.val (S.histories j).mean) e)-_
  simp_rw [coordinate_surrogate_toLp]
  exact hh

end Paper254
#print axioms Paper254.SparseMasterState.step_birth
#print axioms Paper254.SparseMasterState.step_survival
#print axioms Paper254.SparseMasterState.exponential_comparison
