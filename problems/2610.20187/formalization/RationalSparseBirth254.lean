import RationalSparsePrefix254

noncomputable section
namespace Paper254

theorem rationalSparseRun_unborn {d n : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (schedule : RationalSparseSchedule n) (initial : RationalSparseData d n)
    (query : ℕ→RationalGradientQuery d) (i : ℕ) (e : Fin n)
    (hunborn : ∀ t < i,e∉schedule.live t) :
    (rationalSparseRun oracle cfg p lam schedule initial query i).histories e=initial.histories e := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hp := ih (fun t ht=>hunborn t (by omega))
    simp only [rationalSparseRun,rationalSparseStep,if_neg (hunborn i (by omega))]
    exact hp

theorem rationalSparseRun_live_update {d n : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (schedule : RationalSparseSchedule n) (initial : RationalSparseData d n)
    (query : ℕ→RationalGradientQuery d) (i : ℕ) (e : Fin n) (he : e∈schedule.live i) :
    (rationalSparseRun oracle cfg p lam schedule initial query (i+1)).histories e=
      let S := rationalSparseRun oracle cfg p lam schedule initial query i
      rationalHistoryStep oracle (cfg e) (S.histories e) lam
        (query i (rationalSparsePrediction S)) (rationalSparsePrediction S) := by
  simp only [rationalSparseRun,rationalSparseStep,if_pos he]

theorem rationalSparseRun_birth_weight {d n : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (p : ℕ) (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta)
    (lo : Fin n→ℝ) (hi : ℝ) (schedule : RationalSparseSchedule n)
    (hsch : RationalSparseScheduleSpec schedule) (initial : RationalSparseData d n)
    (query : ℕ→RationalGradientQuery d)
    (hstate : ∀ t,RationalSparseInvariant W lo hi (schedule.live t)
      (rationalSparseRun oracle cfg p lam schedule initial query t))
    (hg : ∀ t w,WithLp.toLp 2 (fun j=>(w j:ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j=>(query t w j:ℝ))‖≤G)
    (t : ℕ) (e : Fin n) (he : e∈schedule.live (t+1)) :
    (schedule.share t:ℝ)*(schedule.prior t e:ℝ)/
      (1+3*(schedule.live (t+1)).card*((2:ℝ)^p)⁻¹)≤
      ((rationalSparseRun oracle cfg p lam schedule initial query (t+1)).weights e:ℝ) := by
  let S := rationalSparseRun oracle cfg p lam schedule initial query t
  let g := query t (rationalSparsePrediction S)
  have hg' := hg t _ (hstate t).prediction_feasible
  have hh := rationalMasterUpdate_spec p (schedule.live t) (schedule.live (t+1)) S.weights
    (rationalSparseExponents lam S g) (schedule.prior t) (schedule.share t)
    (hstate t).nonneg (hstate t).total (hstate t).support
    (rationalSparseExponents_bound W hD hG heta lo hi (schedule.live t) S (hstate t) lam hlam g hg')
    (hsch.prior_nonneg t) (hsch.prior_total t) (hsch.share_pos t) (hsch.share_le_one t)
    (hsch.prior_support t)
  exact (hh.2.2.2 e he).2

end Paper254
#print axioms Paper254.rationalSparseRun_unborn
#print axioms Paper254.rationalSparseRun_birth_weight
