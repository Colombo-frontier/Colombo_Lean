import RationalSparseRun254

noncomputable section
open scoped BigOperators
namespace Paper254

def rationalSparseSurrogate {d n : ℕ} (lam : ℚ) (S : RationalSparseData d n)
    (g : Fin d→ℚ) : Loss d :=
  rankOneSurrogate (2*(lam:ℝ)) (WithLp.toLp 2 (fun j=>(g j:ℝ)))
    (WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ)))

theorem rationalSparseExponents_value {d n : ℕ} (lam : ℚ) (S : RationalSparseData d n)
    (g : Fin d→ℚ) (e : Fin n) :
    (rationalSparseExponents lam S g e:ℝ)=-(lam:ℝ)*rationalSparseSurrogate lam S g
      (WithLp.toLp 2 (fun j=>((S.histories e).mean j:ℝ))) := by
  simp only [rationalSparseExponents,Rat.cast_mul,Rat.cast_neg,rationalCoordinateSurrogate_cast]
  rw [coordinate_surrogate_eq]
  rfl

theorem rationalSparseStep_master_regret {d n : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (oracle : RationalProjectionProcedure d) (cfg : Fin n→RationalHistoryParameters)
    (p : ℕ) (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta)
    (lo : Fin n→ℝ) (hi : ℝ) (live next : Finset (Fin n))
    (prior : Fin n→ℚ) (alpha : ℚ) (hp : ∀ e,0≤prior e) (hp1 : ∑ e,prior e=1)
    (ha : 0<alpha) (ha1 : alpha<1) (hprior : ∀ e,0<prior e → e∈next)
    (S : RationalSparseData d n) (hS : RationalSparseInvariant W lo hi live S)
    (g : Fin d→ℚ) (hg : ‖WithLp.toLp 2 (fun j=>(g j:ℝ))‖≤G)
    (e : Fin n) (he : e∈next) (hwe : 0<S.weights e) :
    (lam:ℝ)*(rationalSparseSurrogate lam S g
      (WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ)))-rationalSparseSurrogate lam S g
      (WithLp.toLp 2 (fun j=>((S.histories e).mean j:ℝ))))≤
      Real.log ((rationalSparseStep oracle cfg p lam live next prior alpha S g).weights e:ℝ)-
      Real.log (S.weights e:ℝ)-Real.log (1-(alpha:ℝ))+
      3*(live.card+next.card:ℕ)*((2:ℝ)^p)⁻¹ := by
  let x : Fin n→W.carrier := fun e=>⟨WithLp.toLp 2 (fun j=>((S.histories e).mean j:ℝ)),(hS.histories e).feasible⟩
  have hhalf : (lam:ℝ)=curvature D G eta/2 := by linarith
  have hf : ExpConcaveOn (lam:ℝ) W.carrier (rationalSparseSurrogate lam S g) := by
    change ExpConcaveOn (lam:ℝ) W.carrier (rankOneSurrogate (2*(lam:ℝ)) _ _)
    rw [hlam,hhalf]
    exact surrogate_expConcave W hD hG heta hg hS.prediction_feasible
  have hh := rationalMasterUpdate_regret W p live next S.weights (rationalSparseExponents lam S g)
    prior alpha hS.nonneg hS.total hS.support
    (rationalSparseExponents_bound W hD hG heta lo hi live S hS lam hlam g hg)
    hp hp1 ha ha1 hprior x (lam:ℝ) (rationalSparseSurrogate lam S g) hf
    (rationalSparseExponents_value lam S g) e he hwe
  have hpred : (weightedPrediction (rationalPrior S.weights hS.nonneg hS.total).weight x
      (rationalPrior S.weights hS.nonneg hS.total).nonneg
      (rationalPrior S.weights hS.nonneg hS.total).total).val=
      WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ)) := by
    exact (rationalSparsePrediction_eq S).symm
  rw [hpred] at hh
  exact hh

end Paper254
#print axioms Paper254.rationalSparseStep_master_regret
