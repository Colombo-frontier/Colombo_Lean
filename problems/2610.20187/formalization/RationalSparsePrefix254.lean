import RationalSparseRaw254

noncomputable section
namespace Paper254

def rationalSparseMasterError {n : ℕ} (p : ℕ) (schedule : RationalSparseSchedule n) (t : ℕ) : ℝ :=
  3*((schedule.live t).card+(schedule.live (t+1)).card:ℕ)*((2:ℝ)^p)⁻¹

def rationalSparseDifference {d n : ℕ} (lam : ℚ) (S : RationalSparseData d n)
    (g : Fin d→ℚ) (e : Fin n) : ℝ :=
  rationalSparseSurrogate lam S g (WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ)))-
    rationalSparseSurrogate lam S g (WithLp.toLp 2 (fun j=>((S.histories e).mean j:ℝ)))

/-- Prefix comparison for the actual rational trajectory. Birth mass and
being alive are explicit schedule facts; no prefix regret is assumed. -/
theorem rationalSparseRun_prefix {d n : ℕ} {D G eta : ℝ} (W : Domain d D)
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
    (i length : ℕ) (e : Fin n) (q : ℝ) (hq : 0<q)
    (hbirth : q/(i+1:ℝ)≤((rationalSparseRun oracle cfg p lam schedule initial query i).weights e:ℝ))
    (halive : ∀ k≤length,e∈schedule.live (i+k))
    (hshare : ∀ k<length,(schedule.share (i+k):ℝ)=1/(i+k+2:ℝ)) :
    cumulative (fun k=>let S := rationalSparseRun oracle cfg p lam schedule initial query (i+k)
      rationalSparseDifference lam S (query (i+k) (rationalSparsePrediction S)) e) (length+1)≤
      Real.log (((i+1:ℝ)+length)/q)/(lam:ℝ)+
      cumulative (fun k=>rationalSparseMasterError p schedule (i+k)) (length+1)/(lam:ℝ) := by
  let S := rationalSparseRun oracle cfg p lam schedule initial query
  let grad := fun t=>query t (rationalSparsePrediction (S t))
  let weight := fun k=>(S (i+k)).weights e
  let raw := fun k=>rationalSparseRaw p lam (schedule.live (i+k)) (schedule.live (i+k+1))
    (S (i+k)) (grad (i+k)) e
  let charge := fun k=>rationalSparseDifference lam (S (i+k)) (grad (i+k)) e
  have hlam0 : 0<(lam:ℝ) := by have h := curvature_pos D G eta hD hG heta; linarith
  have hgrad t : ‖WithLp.toLp 2 (fun j=>(grad t j:ℝ))‖≤G :=
    hg t _ (hstate t).prediction_feasible
  have hrprop k (hw : 0<weight k) := rationalSparseRaw_step W hD hG heta p lam hlam lo hi
    (schedule.live (i+k)) (schedule.live (i+k+1)) (S (i+k)) (hstate (i+k))
    (grad (i+k)) (hgrad (i+k)) e hw
  have hsurv k (hk : k<length) :
      ((i+1:ℝ)+k)/((i+1:ℝ)+k+1)*raw k≤(weight (k+1):ℝ) := by
    have hs := rationalSparseRaw_survival oracle cfg p lam (schedule.live (i+k))
      (schedule.live (i+k+1)) (schedule.prior (i+k)) (schedule.share (i+k)) (S (i+k))
      (grad (i+k)) (hstate (i+k)).nonneg (hstate (i+k)).total (hstate (i+k)).support
      (rationalSparseExponents_bound W hD hG heta lo hi (schedule.live (i+k)) (S (i+k))
        (hstate (i+k)) lam hlam (grad (i+k)) (hgrad (i+k)))
      (hsch.prior_nonneg (i+k)) (hsch.prior_total (i+k)) (hsch.share_pos (i+k))
      (hsch.share_le_one (i+k)) (hsch.prior_support (i+k)) e
      (by simpa only [Nat.add_assoc] using halive (k+1) (by omega))
    rw [hshare k hk] at hs
    have he : ((i+1:ℝ)+k)/((i+1:ℝ)+k+1)=1-1/(i+k+2:ℝ) := by field_simp; ring
    rw [he]
    simpa only [weight,raw,S,rationalSparseRun,grad,Nat.add_assoc] using hs
  have hweight : ∀ k≤length,0<weight k := by
    intro k hk
    induction k with
    | zero =>
      have hh : 0<((S i).weights e:ℝ) := (div_pos hq (by positivity)).trans_le hbirth
      exact Rat.cast_pos.mp hh
    | succ k ih =>
      have hw := ih (by omega)
      have hp : 0<raw k := (hrprop k hw).1
      have hratio : 0<((i+1:ℝ)+k)/((i+1:ℝ)+k+1) := by positivity
      exact Rat.cast_pos.mp ((mul_pos hratio hp).trans_le (hsurv k (by omega)))
  have hh := inexact_history_prefix length (i+1:ℝ) q (lam:ℝ)
    (fun k=>(weight k:ℝ)) raw charge (fun k=>rationalSparseMasterError p schedule (i+k))
    (by positivity) hq hlam0 (by simpa only [weight,S,Nat.add_zero] using hbirth)
    (fun k hk=>Rat.cast_pos.mpr (hweight k hk))
    (fun k hk=>(hrprop k (hweight k hk)).1) hsurv
    (fun k hk=>(hrprop k (hweight k hk)).2.2) (hrprop length (hweight length le_rfl)).2.1
  exact hh

end Paper254
#print axioms Paper254.rationalSparseRun_prefix
