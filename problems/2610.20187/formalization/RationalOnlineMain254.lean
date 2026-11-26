import RationalSparseOnline254
import RationalSparseTuning254
import RationalSparseCurved254
import RationalSparseLinear254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T (scaleCount T) D G eta W)

theorem online_clipped (hT : 0 < T) (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (delta : ℝ) (hdelta : 0 < delta)
    (htune : RationalSparseTuning C delta) (f : Fin T → Loss d)
    (hf : ∀ t, AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (u : Fin T → W.carrier)
    (tau : ℝ) (hlo : D/T≤tau) (hhi : tau≤D) :
    regret (C.onlineLearner oracle hspec) f u≤2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
      Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*pathLength u+
        curvature D G eta*G^2*T*tau^2)+delta := by
  let fExt := extendFinite (fun _ => 0) f
  let uExt := extendFinite (C.playedPoint 0) u
  let A := C.forLosses oracle hspec fExt
  have hfExt : ∀ t < T, ExpConcaveOn eta W.carrier (fExt t) := by
    intro t ht
    simpa only [fExt,extendFinite,dif_pos ht] using (hf ⟨t,ht⟩).expConcave
  have hder : ∀ t < T, HasGradientWithinAt (fExt t)
      (WithLp.toLp 2 (fun j => (A.gradient t j : ℝ))) W.carrier (A.playedPoint t).val :=
    C.forLosses_derivative oracle hspec f hcompatible
  have hreg := C.online_regret oracle hspec f u
  change regret (C.onlineLearner oracle hspec) f u=A.cumulativeRegret fExt uExt at hreg
  have hpath : pathLength u=intervalCharge (A.movementLength uExt) 0 (T-1) :=
    pathLength_extension (C.playedPoint 0) u
  by_cases hT2 : 2≤T
  · have hh := A.loss_clipped hT2 fExt hfExt hder htune.grid htune.master_small delta
      htune.local_error htune.master_error uExt tau hlo hhi
    rw [←hpath,←hreg] at hh
    exact hh
  · have hT1 : T=1 := by omega
    subst T
    have hh := A.loss_one_round fExt hfExt hder uExt
    rw [←hreg] at hh
    have hg := Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos
    have hs : 0≤(d+1 : ℝ)*logFactor 1^2/curvature D G eta := by positivity
    have hm : 0≤Real.sqrt (d+1 : ℝ)*logFactor 1^2/(curvature D G eta*tau)*pathLength u := by
      have hdlo : D≤tau := by simpa only [Nat.cast_one,div_one] using hlo
      have htau : 0<tau := C.diameter_pos.trans_le hdlo
      exact mul_nonneg (by positivity) (pathLength_nonneg u)
    have hsm : 0≤curvature D G eta*G^2*(1 : ℕ)*tau^2 := by positivity
    ring_nf at hh hs hm hsm ⊢
    nlinarith

end RationalSparseConstruction

/-- A proper causal `OnlineLearner`, selected before the loss sequence,
with its rational numerical trajectory and finite error budget verified. -/
theorem exists_rational_online_clipped {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (a b : ℕ) (hdim : (d : ℝ)≤(2 : ℝ)^a)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhib : (hi : ℝ)≤(2 : ℝ)^b)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (gradientOracle : RationalLossGradientOracle d)
    (hgradient : RationalLossGradientOracleSpec W G eta gradientOracle)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ A : OnlineLearner W T, ∀ f : Fin T → Loss d,
      (∀ t, AdmissibleLoss W G eta (f t)) →
      (∀ t, RationalLossCompatible W gradientOracle (f t)) → ∀ u : Fin T → W.carrier,
        regret A f u≤G*D*T ∧ ∀ tau : ℝ, D/T≤tau → tau≤D →
          regret A f u≤2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
            Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*pathLength u+
              curvature D G eta*G^2*T*tau^2)+delta := by
  obtain ⟨C,_hCo,_hCw,_hCh,_hClam,htune⟩ := exists_rational_sparse_tuning hd hT W hD hG heta
    a b hdim oracle hspec hi hhi hhib lam hlam w0 hw0 delta hdelta
  refine ⟨C.onlineLearner gradientOracle hgradient,?_⟩
  intro f hf hcompatible u
  refine ⟨linear_regret_bound _ f u hG.le hf,?_⟩
  exact C.online_clipped hT gradientOracle hgradient delta hdelta htune f hf hcompatible u

theorem exists_rational_online_curved {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (a b : ℕ) (hdim : (d : ℝ)≤(2 : ℝ)^a)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhib : (hi : ℝ)≤(2 : ℝ)^b)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (gradientOracle : RationalLossGradientOracle d)
    (hgradient : RationalLossGradientOracleSpec W G eta gradientOracle)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ A : OnlineLearner W T, ∀ f : Fin T → Loss d,
      (∀ t, AdmissibleLoss W G eta (f t)) →
      (∀ t, RationalLossCompatible W gradientOracle (f t)) → ∀ u : Fin T → W.carrier,
        pathLength u≤curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2) →
        regret A f u≤6144*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
          explicitCurvedRate (curvature D G eta) G d T (pathLength u))+delta := by
  obtain ⟨A,hA⟩ := exists_rational_online_clipped hd hT W hD hG heta a b hdim oracle hspec
    hi hhi hhib lam hlam w0 hw0 gradientOracle hgradient delta hdelta
  refine ⟨A,?_⟩
  intro f hf hcompatible u hsmall
  exact clipped_numeric_explicit D G eta (regret A f u) (pathLength u) delta d T hD hG heta hd hT
    (pathLength_nonneg u) hsmall (hA f hf hcompatible u).2

end Paper254
#print axioms Paper254.exists_rational_online_clipped
#print axioms Paper254.exists_rational_online_curved
