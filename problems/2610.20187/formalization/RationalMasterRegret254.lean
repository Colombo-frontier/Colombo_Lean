import RationalMasterUpdate254
import HistoryPrefix254

open scoped BigOperators
namespace Paper254

theorem log_relative_survival (v q a B C : ℝ) (hv : 0<v) (ha : 0<a)
    (hB : 0<B) (hC : 0<C) (h : a*v/(B*C)≤q) :
    0<q ∧ Real.log v≤Real.log q-Real.log a+Real.log (B*C) := by
  have hl : 0<a*v/(B*C) := by positivity
  have hq := hl.trans_le h
  have hh := Real.log_le_log hl h
  rw [Real.log_div (by positivity) (by positivity),Real.log_mul ha.ne' hv.ne'] at hh
  exact ⟨hq,by linarith⟩

/-- The comparison is with losses at the actual feasible weighted prediction.
The update uses rational exponent inputs and both rounds of live-set rounding. -/
theorem rationalMasterUpdate_regret {d n : ℕ} {D : ℝ} (W : Domain d D)
    (p : ℕ) (live next : Finset (Fin n)) (w z prior : Fin n→ℚ) (alpha : ℚ)
    (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1) (hsupport : ∀ j,j∉live → w j=0)
    (hz : ∀ j,|(z j:ℝ)|≤1/2) (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1)
    (ha : 0<alpha) (ha1 : alpha<1) (hprior : ∀ j,0<prior j → j∈next)
    (x : Fin n→W.carrier) (lam : ℝ) (f : Loss d) (hf : ExpConcaveOn lam W.carrier f)
    (hzvalue : ∀ j,(z j:ℝ)=-lam*f (x j).val) (j : Fin n) (hj : j∈next) (hwj : 0<w j) :
    lam*(f (weightedPrediction (rationalPrior w hw hw1).weight x
      (rationalPrior w hw hw1).nonneg (rationalPrior w hw hw1).total).val-f (x j).val)≤
      Real.log (rationalMasterUpdate p live next w z prior alpha j:ℝ)-Real.log (w j:ℝ)-
      Real.log (1-(alpha:ℝ))+3*(live.card+next.card:ℕ)*((2:ℝ)^p)⁻¹ := by
  let P := rationalPrior w hw hw1
  let v := P.exponential (-1) (fun k=>(z k:ℝ))
  have hraw : v.weight j=exponentialUpdate lam P.weight (fun k=>f (x k).val) j := by
    simp only [v,ProbabilityWeights.exponential,exponentialUpdate,exponentialNormalizer]
    simp_rw [hzvalue]
    simp only [neg_neg,mul_one,one_mul]
  have hwjr : 0<P.weight j := Rat.cast_pos.mpr hwj
  have hv : 0<v.weight j := by
    rw [hraw]
    exact div_pos (mul_pos hwjr (Real.exp_pos _))
      (exponentialNormalizer_pos lam P.weight _ P.nonneg j hwjr)
  have hs := rationalMasterUpdate_spec p live next w z prior alpha hw hw1 hsupport hz hp hp1 ha ha1.le hprior
  have ha0 : 0<1-(alpha:ℝ) := by exact_mod_cast (sub_pos.mpr ha1)
  have hl := log_relative_survival (v.weight j) (rationalMasterUpdate p live next w z prior alpha j:ℝ)
    (1-(alpha:ℝ)) (1+3*live.card*((2:ℝ)^p)⁻¹) (1+3*next.card*((2:ℝ)^p)⁻¹)
    hv ha0 (by positivity) (by positivity) (hs.2.2.2 j hj).1
  have hx := exponential_update_one_step P.weight x P.nonneg P.total hf j hwjr
  rw [←hraw] at hx
  have hb := rationalMasterUpdate_log_overhead p live.card next.card
  change _≤Real.log (v.weight j)-Real.log (w j:ℝ) at hx
  linarith [hl.2]

/-- The birth penalty and all per-round numerical penalties are paid once
in the prefix telescope. -/
theorem inexact_history_prefix (n : ℕ) (i q lam : ℝ) (p raw r error : ℕ→ℝ)
    (hi : 0 < i) (hq : 0 < q) (hlam : 0 < lam) (hbirth : q/i≤p 0)
    (hp : ∀ t≤n,0<p t) (hr : ∀ t≤n,0<raw t)
    (hsurvive : ∀ t<n,(i+t)/(i+t+1)*raw t≤p (t+1))
    (hstep : ∀ t≤n,lam*r t≤Real.log (raw t)-Real.log (p t)+error t)
    (hterminal : raw n≤1) :
    cumulative r (n+1)≤Real.log ((i+n)/q)/lam+cumulative error (n+1)/lam := by
  have hh := history_prefix_overhead n i q lam p raw (fun t=>r t-error t/lam)
    hi hq hlam hbirth hp hr hsurvive
    (by intro t ht; have hs := hstep t ht; field_simp; nlinarith) hterminal
  have he : cumulative (fun t=>r t-error t/lam) (n+1)=
      cumulative r (n+1)-cumulative error (n+1)/lam := by
    simp only [cumulative,Finset.sum_sub_distrib,Finset.sum_div]
  rw [he] at hh
  linarith

end Paper254
#print axioms Paper254.rationalMasterUpdate_regret
#print axioms Paper254.inexact_history_prefix
