import SparseTrajectory254

noncomputable section
namespace Paper254

theorem SparseMasterState.raw_weight_pos {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (f : Loss d) (e : HistoryExpert T K)
    (he : 0 < S.weights.weight e) :
    0 < (S.rawWeights (G := G) (η := η) f).weight e := by
  change 0 < S.weights.weight e*Real.exp _/exponentialNormalizer _ S.weights.weight _
  exact div_pos (mul_pos he (Real.exp_pos _))
    (exponentialNormalizer_pos _ _ _ S.weights.nonneg e he)

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "S" => sparseTrajectory (T := T) W hD hG hη w0 q hq f

theorem sparseHistory_birth_positive (e : HistoryExpert T K) :
    0 < (S e.1.val).weights.weight e :=
  lt_of_lt_of_le (by positivity) (sparseHistory_birth_weight W hD hG hη w0 q hq f e)

theorem sparseHistory_weight_positive (e : HistoryExpert T K) (n : ℕ)
    (hborn : e.1.val ≤ n) (hnT : n ≤ T) (hactive : HistoryActive (n+1) (expertBirth e)) :
    0 < (S n).weights.weight e := by
  induction n with
  | zero =>
    have he : e.1.val = 0 := by omega
    simpa only [he] using sparseHistory_birth_positive W hD hG hη w0 q hq f e
  | succ n ih =>
    by_cases hnew : e.1.val = n+1
    · simpa only [hnew] using sparseHistory_birth_positive W hD hG hη w0 q hq f e
    have hn : n < T := by omega
    have hprev : HistoryActive (n+1) (expertBirth e) :=
      historyActive_prefix hactive (by dsimp [expertBirth]; omega) (by omega)
    have hp := ih (by omega) (by omega) hprev
    have hr := (S n).raw_weight_pos (G := G) (η := η) (f n) e hp
    have hs := (S n).step_survival hD hG hη q hq ⟨n,hn⟩ (f n) e
      ((mem_liveExperts e).mpr hactive)
    have hc : 0 < 1-1/(n+2 : ℝ) := by
      have hh : 1/(n+2 : ℝ) < 1 := (div_lt_one (by positivity)).mpr
        (by linarith [Nat.cast_nonneg n (α := ℝ)])
      linarith
    rw [sparseTrajectory_succ W hD hG hη w0 q hq f n hn]
    exact lt_of_lt_of_le (mul_pos hc hr) hs

theorem sparseHistory_survival (e : HistoryExpert T K) (n : ℕ) (hn : n < T)
    (hactive : HistoryActive (n+2) (expertBirth e)) :
    ((n+1 : ℝ)/(n+2 : ℝ))*((S n).rawWeights (G := G) (η := η) (f n)).weight e ≤
      (S (n+1)).weights.weight e := by
  rw [sparseTrajectory_succ W hD hG hη w0 q hq f n hn]
  have hh := (S n).step_survival hD hG hη q hq ⟨n,hn⟩ (f n) e
    ((mem_liveExperts e).mpr hactive)
  have hc : (n+1 : ℝ)/(n+2 : ℝ) = 1-1/(n+2 : ℝ) := by
    field_simp
    ring
  rw [hc]
  exact hh

end Trajectory
end Paper254
#print axioms Paper254.sparseHistory_weight_positive
#print axioms Paper254.sparseHistory_survival
