import RationalSparseMaster254

noncomputable section
open scoped BigOperators
namespace Paper254

def rationalSparseRaw {d n : ℕ} (p : ℕ) (lam : ℚ) (live next : Finset (Fin n))
    (S : RationalSparseData d n) (g : Fin d→ℚ) (e : Fin n) : ℝ :=
  (rationalLiveSoftmax p live S.weights (rationalSparseExponents lam S g) e:ℝ)/
    (1+3*next.card*((2:ℝ)^p)⁻¹)

theorem rationalSparseRaw_step {d n : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (p : ℕ) (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta)
    (lo : Fin n→ℝ) (hi : ℝ) (live next : Finset (Fin n))
    (S : RationalSparseData d n) (hS : RationalSparseInvariant W lo hi live S)
    (g : Fin d→ℚ) (hg : ‖WithLp.toLp 2 (fun j=>(g j:ℝ))‖≤G)
    (e : Fin n) (hwe : 0<S.weights e) :
    0<rationalSparseRaw p lam live next S g e ∧ rationalSparseRaw p lam live next S g e≤1 ∧
    (lam:ℝ)*(rationalSparseSurrogate lam S g
      (WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ)))-rationalSparseSurrogate lam S g
      (WithLp.toLp 2 (fun j=>((S.histories e).mean j:ℝ))))≤
      Real.log (rationalSparseRaw p lam live next S g e)-Real.log (S.weights e:ℝ)+
      3*(live.card+next.card:ℕ)*((2:ℝ)^p)⁻¹ := by
  let P := rationalPrior S.weights hS.nonneg hS.total
  let v := P.exponential (-1) (fun k=>(rationalSparseExponents lam S g k:ℝ))
  let B : ℝ := 1+3*live.card*((2:ℝ)^p)⁻¹
  let C : ℝ := 1+3*next.card*((2:ℝ)^p)⁻¹
  let x : Fin n→W.carrier := fun k=>⟨WithLp.toLp 2 (fun j=>((S.histories k).mean j:ℝ)),(hS.histories k).feasible⟩
  have hhalf : (lam:ℝ)=curvature D G eta/2 := by linarith
  have hf : ExpConcaveOn (lam:ℝ) W.carrier (rationalSparseSurrogate lam S g) := by
    change ExpConcaveOn (lam:ℝ) W.carrier (rankOneSurrogate (2*(lam:ℝ)) _ _)
    rw [hlam,hhalf]
    exact surrogate_expConcave W hD hG heta hg hS.prediction_feasible
  have hraw : v.weight e=exponentialUpdate (lam:ℝ) P.weight
      (fun k=>rationalSparseSurrogate lam S g (x k).val) e := by
    simp only [v,ProbabilityWeights.exponential,exponentialUpdate,exponentialNormalizer]
    simp_rw [rationalSparseExponents_value]
    simp only [neg_neg,one_mul]
    rfl
  have hwpos : 0<P.weight e := Rat.cast_pos.mpr hwe
  have hv : 0<v.weight e := by
    rw [hraw]
    exact div_pos (mul_pos hwpos (Real.exp_pos _))
      (exponentialNormalizer_pos _ _ _ P.nonneg e hwpos)
  have hs := rationalLiveSoftmax_spec p live S.weights (rationalSparseExponents lam S g)
    hS.nonneg hS.total hS.support (rationalSparseExponents_bound W hD hG heta lo hi live S hS lam hlam g hg)
  have hlow : v.weight e/(B*C)≤rationalSparseRaw p lam live next S g e := by
    change v.weight e/(B*C)≤_ / C
    rw [←div_div]
    exact div_le_div_of_nonneg_right (hs.2.2.2.1 e) (by dsimp [C]; positivity)
  have hpos : 0<rationalSparseRaw p lam live next S g e :=
    (div_pos hv (by dsimp [B,C]; positivity)).trans_le hlow
  have hone : (rationalLiveSoftmax p live S.weights (rationalSparseExponents lam S g) e:ℝ)≤1 := by
    exact (rationalPrior _ hs.2.1 hs.1).weight_le_one e
  have hrawle : rationalSparseRaw p lam live next S g e≤1 := by
    change _/C≤1
    apply (div_le_one (by dsimp [C]; positivity)).mpr
    exact hone.trans (le_add_of_nonneg_right (by positivity))
  have hlog := Real.log_le_log (div_pos hv (by dsimp [B,C]; positivity)) hlow
  rw [Real.log_div hv.ne' (by dsimp [B,C]; positivity)] at hlog
  have hx := exponential_update_one_step P.weight x P.nonneg P.total hf e hwpos
  rw [←hraw] at hx
  have hpred : (weightedPrediction P.weight x P.nonneg P.total).val=
      WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ)) := (rationalSparsePrediction_eq S).symm
  rw [hpred] at hx
  have hb := rationalMasterUpdate_log_overhead p live.card next.card
  change Real.log (B*C)≤_ at hb
  refine ⟨hpos,hrawle,?_⟩
  change _≤Real.log (v.weight e)-Real.log (S.weights e:ℝ) at hx
  linarith

theorem rationalSparseRaw_survival {d n : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha : ℚ)
    (S : RationalSparseData d n) (g : Fin d→ℚ)
    (hw : ∀ e,0≤S.weights e) (hw1 : ∑ e,S.weights e=1)
    (hws : ∀ e,e∉live → S.weights e=0)
    (hz : ∀ e,|(rationalSparseExponents lam S g e:ℝ)|≤1/2)
    (hp : ∀ e,0≤prior e) (hp1 : ∑ e,prior e=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ e,0<prior e → e∈next) (e : Fin n) (he : e∈next) :
    (1-(alpha:ℝ))*rationalSparseRaw p lam live next S g e≤
      ((rationalSparseStep oracle cfg p lam live next prior alpha S g).weights e:ℝ) := by
  have hs := rationalLiveSoftmax_spec p live S.weights (rationalSparseExponents lam S g) hw hw1 hws hz
  have hr := rationalRoundedPruneShare_spec p (rationalLiveSoftmax p live S.weights (rationalSparseExponents lam S g))
    prior alpha next hs.2.1 hs.1 hp hp1 ha ha1 hprior
  have hh := (hr.2.2.2 e he).1
  change (1-(alpha:ℝ))*(_/_ )≤_
  rw [←mul_div_assoc]
  exact hh

end Paper254
#print axioms Paper254.rationalSparseRaw_step
#print axioms Paper254.rationalSparseRaw_survival
