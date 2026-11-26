import RationalSparseLearner254

open scoped BigOperators
namespace Paper254

structure RationalSparseSchedule (n : ℕ) where
  live : ℕ→Finset (Fin n)
  prior : ℕ→Fin n→ℚ
  share : ℕ→ℚ

structure RationalSparseScheduleSpec {n : ℕ} (schedule : RationalSparseSchedule n) : Prop where
  prior_nonneg : ∀ t e,0≤schedule.prior t e
  prior_total : ∀ t,∑ e,schedule.prior t e=1
  prior_support : ∀ t e,0<schedule.prior t e → e∈schedule.live (t+1)
  share_pos : ∀ t,0<schedule.share t
  share_le_one : ∀ t,schedule.share t≤1

abbrev RationalGradientQuery (d : ℕ) := (Fin d→ℚ)→(Fin d→ℚ)

def rationalSparseRun {d n : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (schedule : RationalSparseSchedule n) (initial : RationalSparseData d n)
    (query : ℕ→RationalGradientQuery d) : ℕ→RationalSparseData d n
  | 0 => initial
  | t+1 => let S := rationalSparseRun oracle cfg p lam schedule initial query t
           let g := query t (rationalSparsePrediction S)
           rationalSparseStep oracle cfg p lam (schedule.live t) (schedule.live (t+1))
             (schedule.prior t) (schedule.share t) S g

theorem rationalSparseRun_invariant {d n : ℕ} (hd : 0<d) {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (hlam : 2*(lam:ℝ)=curvature D G eta) (lo : Fin n→ℝ) (hi : ℝ)
    (hlo : ∀ e,0<lo e) (hhi : 0<hi) (hguard : ∀ e,UniformHistoryGuards d (cfg e) (lo e) hi)
    (schedule : RationalSparseSchedule n) (hsch : RationalSparseScheduleSpec schedule)
    (initial : RationalSparseData d n) (hinit : RationalSparseInvariant W lo hi (schedule.live 0) initial)
    (query : ℕ→RationalGradientQuery d)
    (hg : ∀ t w,WithLp.toLp 2 (fun j=>(w j:ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j=>(query t w j:ℝ))‖≤G) :
    ∀ t,RationalSparseInvariant W lo hi (schedule.live t)
      (rationalSparseRun oracle cfg p lam schedule initial query t) := by
  intro t
  induction t with
  | zero => exact hinit
  | succ t ih =>
    exact rationalSparseStep_preserves hd W hD hG heta oracle hspec cfg p lam hlam lo hi hlo hhi hguard
      (schedule.live t) (schedule.live (t+1)) (schedule.prior t) (schedule.share t)
      (hsch.prior_nonneg t) (hsch.prior_total t) (hsch.share_pos t) (hsch.share_le_one t)
      (hsch.prior_support t) _ ih _ (hg t _ ih.prediction_feasible)

theorem rationalSparseRun_causal {d n : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (schedule : RationalSparseSchedule n) (initial : RationalSparseData d n)
    (query other : ℕ→RationalGradientQuery d) (t : ℕ)
    (heq : ∀ k<t,∀ w,query k w=other k w) :
    rationalSparseRun oracle cfg p lam schedule initial query t=
      rationalSparseRun oracle cfg p lam schedule initial other t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (fun k hk=>heq k (by omega))
    simp only [rationalSparseRun,hp,heq t (by omega)]

def initialRationalSparse {d n : ℕ} (w0 : Fin d→ℚ) (hi : ℚ) (weights : Fin n→ℚ) :
    RationalSparseData d n := ⟨fun _=>rationalHistoryInitial w0 hi,weights⟩

theorem initialRationalSparse_invariant {d n : ℕ} {D : ℝ} (W : Domain d D)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (hi : ℚ) (hhi : 0<(hi:ℝ)) (lo : Fin n→ℚ) (hlohi : ∀ e,(lo e:ℝ)≤(hi:ℝ))
    (live : Finset (Fin n)) (weights : Fin n→ℚ) (hw : ∀ e,0≤weights e)
    (hw1 : ∑ e,weights e=1) (hws : ∀ e,e∉live → weights e=0) :
    RationalSparseInvariant W (fun e=>(lo e:ℝ)) (hi:ℝ) live (initialRationalSparse w0 hi weights) :=
  ⟨fun e=>rationalHistoryInitial_invariant W w0 hw0 (lo e) hi hhi (hlohi e),hw,hw1,hws⟩

end Paper254
#print axioms Paper254.rationalSparseRun_invariant
#print axioms Paper254.rationalSparseRun_causal
