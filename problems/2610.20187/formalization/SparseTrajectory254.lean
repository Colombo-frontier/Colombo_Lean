import SparseMasterStep254

noncomputable section
namespace Paper254

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "S" => sparseTrajectory (T := T) W hD hG hη w0 q hq f

theorem sparseTrajectory_succ (n : ℕ) (hn : n < T) :
    S (n+1) = (S n).step hD hG hη q hq ⟨n,hn⟩ (f n) := by
  rw [sparseTrajectory, dif_pos hn]

theorem sparseHistory_before_birth (e : HistoryExpert T K) (n : ℕ) (hn : n ≤ e.1.val) :
    (S n).histories e = isotropicGaussian w0.val D hD := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heT := e.1.isLt
    have hnT : n < T := by omega
    have hnot : e ∉ liveExperts T K (n+1) := by
      intro he
      have hh := ((mem_liveExperts e).mp he).2.1
      dsimp [expertBirth] at hh
      omega
    rw [sparseTrajectory_succ W hD hG hη w0 q hq f n hnT,
      SparseMasterState.step_histories, if_neg hnot]
    exact ih (by omega)

theorem sparseHistory_birth_weight (e : HistoryExpert T K) :
    (1/(K+1 : ℝ))/(e.1.val+1 : ℝ) ≤ (S e.1.val).weights.weight e := by
  rcases e with ⟨⟨i, hi⟩, k⟩
  cases i with
  | zero => simp [sparseTrajectory, initialSparseState, birthPrior]
  | succ n =>
    have hnT : n < T := by omega
    rw [sparseTrajectory_succ W hD hG hη w0 q hq f n hnT]
    have hh := (S n).step_birth hD hG hη q hq ⟨n,hnT⟩ (f n) k
    convert hh using 1 <;> push_cast <;> ring

def actualSparseGradient (n : ℕ) : Space d := selectedGradient W G (f n) (S n).prediction

theorem sparseHistory_identification (e : HistoryExpert T K) (n : ℕ)
    (hnT : e.1.val+n ≤ T) (hactive : HistoryActive (e.1.val+n+1) (expertBirth e)) :
    (S (e.1.val+n)).histories e =
      gaussianHistory W hD w0 (curvature D G η/2) (q e.2)
        (le_of_lt (div_pos (curvature_pos D G η hD hG hη) (by norm_num))) (hq e.2)
        (fun j => actualSparseGradient (T := T) W hD hG hη w0 q hq f (e.1.val+j))
        (fun j => (S (e.1.val+j)).prediction) n := by
  induction n with
  | zero =>
    simpa [gaussianHistory] using sparseHistory_before_birth W hD hG hη w0 q hq f e e.1.val le_rfl
  | succ n ih =>
    have hn : e.1.val+n < T := by omega
    have hprev : HistoryActive (e.1.val+n+1) (expertBirth e) :=
      historyActive_prefix hactive (by dsimp [expertBirth]; omega) (by omega)
    have hrec := ih (by omega) hprev
    have hnext : e.1.val+(n+1) = (e.1.val+n)+1 := by omega
    rw [hnext, sparseTrajectory_succ W hD hG hη w0 q hq f (e.1.val+n) hn,
      SparseMasterState.step_histories, if_pos ((mem_liveExperts e).mpr hprev), hrec]
    rfl

end Trajectory
end Paper254
#print axioms Paper254.sparseHistory_before_birth
#print axioms Paper254.sparseHistory_birth_weight
#print axioms Paper254.sparseHistory_identification
