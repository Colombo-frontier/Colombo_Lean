import SparseTrajectory254
import SparseCounts254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem ProbabilityWeights.pruneShare_zero {ι : Type*} [Fintype ι]
    (p prior : ProbabilityWeights ι) (α : ℝ) (ha : 0 < α) (hb : α ≤ 1)
    (live : Finset ι) (hprior : ∀ j, 0 < prior.weight j → j ∈ live)
    (j : ι) (hj : j ∉ live) :
    (p.pruneShare prior α ha hb live hprior).weight j = 0 := by
  classical
  simp [pruneShare,prunedMixtureMass,hj]

theorem sparseTrajectory_support {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)
    (n : ℕ) (hn : n ≤ T) (e : HistoryExpert T K)
    (he : e ∉ liveExperts T K (n+1)) :
    (sparseTrajectory (T := T) W hD hG hη w0 q hq f n).weights.weight e = 0 := by
  cases n with
  | zero =>
    have hne : e.1 ≠ (⟨0,by omega⟩ : Fin (T+1)) := by
      intro hh
      apply he
      apply (mem_liveExperts e).mpr
      simp only [expertBirth,hh]
      exact historyActive_birth 1 (by omega)
    change (if e.1 = (⟨0,by omega⟩ : Fin (T+1)) then 1/(K+1 : ℝ) else 0) = 0
    rw [if_neg hne]
  | succ n =>
    rw [sparseTrajectory_succ W hD hG hη w0 q hq f n (by omega)]
    have he' : e ∉ liveExperts T K (n+2) := by simpa only [Nat.add_assoc] using he
    simp [SparseMasterState.step,ProbabilityWeights.pruneShare,
      ProbabilityWeights.prunedMixtureMass,he']

theorem SparseMasterState.prediction_eq_of_live {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S R : SparseMasterState W T K)
    (hw : ∀ e, S.weights.weight e = R.weights.weight e)
    (hz : ∀ e, e ∉ liveExperts T K t → S.weights.weight e = 0)
    (hh : ∀ e, e ∈ liveExperts T K t → S.histories e = R.histories e) :
    S.prediction = R.prediction := by
  classical
  apply Subtype.ext
  change (∑ e, S.weights.weight e • WithLp.toLp 2 (S.histories e).mean) =
    ∑ e, R.weights.weight e • WithLp.toLp 2 (R.histories e).mean
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e ∈ liveExperts T K t
  · rw [hw e,hh e he]
  · rw [← hw e,hz e he]
    simp

theorem SparseMasterState.rawWeights_eq_of_live {d T K t : ℕ} {D G η : ℝ} {W : Domain d D}
    (S R : SparseMasterState W T K) (f : Loss d)
    (hw : ∀ e, S.weights.weight e = R.weights.weight e)
    (hz : ∀ e, e ∉ liveExperts T K t → S.weights.weight e = 0)
    (hh : ∀ e, e ∈ liveExperts T K t → S.histories e = R.histories e) :
    ∀ e, (S.rawWeights (G := G) (η := η) f).weight e =
      (R.rawWeights (G := G) (η := η) f).weight e := by
  classical
  have hp := S.prediction_eq_of_live R hw hz hh
  have hm : ∀ e, S.weights.weight e * Real.exp (-(curvature D G η/2) *
      coordinateSurrogate (curvature D G η) (selectedGradient W G f S.prediction)
        S.prediction.val (S.histories e).mean) =
    R.weights.weight e * Real.exp (-(curvature D G η/2) *
      coordinateSurrogate (curvature D G η) (selectedGradient W G f R.prediction)
        R.prediction.val (R.histories e).mean) := by
    intro e
    by_cases he : e ∈ liveExperts T K t
    · rw [hw e,hp,hh e he]
    · rw [← hw e,hz e he]
      simp
  intro e
  change _ / exponentialNormalizer _ _ _ = _ / exponentialNormalizer _ _ _
  unfold exponentialNormalizer
  simp_rw [hm]

def SparseMasterState.erase {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (w0 : W.carrier) : SparseMasterState W T K := by
  classical
  refine ⟨fun e => if e ∈ liveExperts T K t then S.histories e else isotropicGaussian w0.val D hD,?_,S.weights⟩
  intro e
  dsimp only
  split_ifs
  · exact S.feasible e
  · exact w0.property

theorem actual_sparse_erasure_prediction {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)
    (n : ℕ) (hn : n ≤ T) :
    let S := sparseTrajectory (T := T) W hD hG hη w0 q hq f n
    S.prediction = (S.erase (t := n+1) hD w0).prediction := by
  classical
  dsimp only
  apply SparseMasterState.prediction_eq_of_live (t := n+1)
  · intro e; rfl
  · exact sparseTrajectory_support W hD hG hη w0 q hq f n hn
  · intro e he
    simp [SparseMasterState.erase,he]

/-- An expert present next round but absent now must be a new birth;
expired experts can never return. -/
theorem next_live_or_birth {T K n : ℕ} (e : HistoryExpert T K)
    (he : e ∈ liveExperts T K (n+2)) :
    e ∈ liveExperts T K (n+1) ∨ e.1.val = n+1 := by
  by_cases hb : expertBirth e ≤ n+1
  · exact Or.inl ((mem_liveExperts e).mpr
      (historyActive_prefix ((mem_liveExperts e).mp he) hb (by omega)))
  · right
    have hh := ((mem_liveExperts e).mp he).2.1
    dsimp [expertBirth] at *
    omega

end Paper254
#print axioms Paper254.actual_sparse_erasure_prediction
