import RationalMaterializedOnline254
import AnytimeClipped254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem padded_rational_compatible {d m H : ℕ} {D G eta : ℝ} {W : Domain d D}
    (oracle : RationalLossGradientOracle d) (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (f : Fin m → Loss d) (hf : ∀ t, RationalLossCompatible W oracle (f t)) :
    ∀ t : Fin H, RationalLossCompatible W oracle (paddedLoss f t) := by
  intro t
  by_cases ht : t.val < m
  · simpa only [paddedLoss,dif_pos ht] using hf ⟨t.val,ht⟩
  · simpa only [paddedLoss,dif_neg ht] using hspec.zero_gradient

def rationalDoublingFamily {d : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W)
    (roundCost projectionCost gradientCost : ℕ) (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) : (H : ℕ) → OnlineLearner W H :=
  fun H => (I H).construction.materializedLearner roundCost projectionCost gradientCost oracle hspec

theorem rational_prefix_clipped {d H m : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W)
    (roundCost projectionCost gradientCost : ℕ) (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle)
    (hm0 : 0 < m) (hm : m≤H) (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : ((2 : ℝ)^(I H).s)⁻¹≤((I H).lam : ℝ)*delta/(2*H))
    (f : Fin m → Loss d) (hf : ∀ t, AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (u : Fin m → W.carrier)
    (tau : ℝ) (htau : 0 < tau) (hhi : tau≤D) :
    regret (prefixLearner (rationalDoublingFamily I roundCost projectionCost gradientCost oracle hspec H) hm) f u≤
      2048*((d+1 : ℝ)*logFactor H^2/curvature D G eta+
        Real.sqrt (d+1 : ℝ)*logFactor H^2/(curvature D G eta*tau)*pathLength u+
          curvature D G eta*G^2*((H : ℝ)*tau^2+D^2/H))+delta := by
  have hH : 0<H := lt_of_lt_of_le hm0 hm
  have hHr : (0 : ℝ)<H := by exact_mod_cast hH
  have hH1 : (1 : ℝ)≤H := by exact_mod_cast hH
  have hd := (I H).diameter_pos
  have hg := (I H).gradient_pos
  have heta := (I H).curvature_pos
  have hh := (I H).regret_clipped hH oracle hspec delta hdelta hbudget
    (paddedLoss f) (padded_admissible W hg.le f hf)
    (padded_rational_compatible oracle hspec f hcompatible) (paddedComparator hm0 u)
    (max tau (D/H)) (le_max_right _ _) (max_le hhi (div_le_self hd.le hH1))
  rw [prefix_regret _ hm hm0 f u,padded_pathLength hm hm0 u] at hh
  unfold rationalDoublingFamily
  rw [(I H).construction.materializedLearner_eq]
  have hgamma := curvature_pos D G eta hd hg heta
  have hmove := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left
    (show 0≤Real.sqrt (d+1 : ℝ)*logFactor H^2 by positivity) (mul_pos hgamma htau)
    (mul_le_mul_of_nonneg_left (le_max_left tau (D/H)) hgamma.le)) (pathLength_nonneg u)
  have hsm := mul_le_mul_of_nonneg_left (epoch_clipped_smoothing H D tau hHr hd.le htau.le)
    (show 0≤curvature D G eta*G^2 by positivity)
  change regret (prefixLearner ((I H).learner oracle hspec) hm) f u≤_
  nlinarith

/-- Doubling spends a summable numerical error budget; the learner is
specified before the terminal horizon and uses the materialized rational code. -/
theorem rational_anytime_clipped {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (I : (H : ℕ) → ExplicitRationalSparseInput d H D G eta W)
    (roundCost projectionCost gradientCost : ℕ) (oracle : RationalLossGradientOracle d)
    (hspec : RationalLossGradientOracleSpec W G eta oracle) (hT : 0 < T)
    (delta : ℝ) (hdelta : 0 < delta)
    (hbudget : ∀ j : ℕ, ((2 : ℝ)^(I (2^j)).s)⁻¹≤
      ((I (2^j)).lam : ℝ)*(delta/(2 : ℝ)^(j+1))/(2*(2^j : ℕ)))
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W oracle (f t)) (u : Fin T → W.carrier)
    (tau : ℝ) (htau : 0 < tau) (hhi : tau≤D) :
    regret (anytimeRestriction (doublingLearner
      (rationalDoublingFamily I roundCost projectionCost gradientCost oracle hspec)) T) f u≤
      2048*((epochCount T : ℝ)*(d+1 : ℝ)*logFactor T^2/curvature D G eta+
        Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*pathLength u+
          curvature D G eta*G^2*(2*T*tau^2+2*D^2))+delta := by
  let gamma := curvature D G eta
  let A := (d+1 : ℝ)*logFactor T^2/gamma
  let B := Real.sqrt (d+1 : ℝ)*logFactor T^2/(gamma*tau)
  let H : Fin (epochCount T) → ℝ := fun j => (2^j.val : ℕ)
  let P := fun j : Fin (epochCount T) => pathLength (epochComparator u j)
  let E := fun j : Fin (epochCount T) => delta/(2 : ℝ)^(j.val+1)
  have hgamma : 0<gamma := curvature_pos D G eta (I T).diameter_pos (I T).gradient_pos (I T).curvature_pos
  have hB : 0≤B := by dsimp [B]; positivity
  have hsumH : (∑ j,H j)≤2*T := by
    dsimp [H]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    rw [Fin.sum_univ_eq_sum_range]
    exact doubling_planned_time T hT
  have hsumR : (∑ j,1/H j)≤2 := by simpa [H] using dyadic_reciprocal_sum (epochCount T)
  have hsumP : (∑ j,P j)≤pathLength u := epoch_path_sum u
  have hsumE : (∑ j,E j)≤delta := by
    dsimp [E]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => delta/(2 : ℝ)^(j+1)) (epochCount T)]
    exact doubling_error_sum delta hdelta.le (epochCount T)
  rw [doubling_regret_decomposition]
  have hlocal : ∀ j : Fin (epochCount T),
      regret (prefixLearner (rationalDoublingFamily I roundCost projectionCost gradientCost oracle hspec (2^j.val))
        (min_le_left _ _)) (epochLoss f j) (epochComparator u j)≤
          2048*(A+B*P j+gamma*G^2*(H j*tau^2+D^2/H j))+E j := by
    intro j
    have hh := rational_prefix_clipped I roundCost projectionCost gradientCost oracle hspec
      (epoch_length_pos hT j) (min_le_left _ _) (E j) (by dsimp [E]; positivity) (hbudget j.val)
      (epochLoss f j) (fun k => hf (epochRound ⟨j,k⟩))
      (fun k => hcompatible (epochRound ⟨j,k⟩)) (epochComparator u j) tau htau hhi
    have hlog := logFactor_mono (by positivity : 0<2^j.val) (epoch_horizon_le hT j)
    have hlog0 : 0≤logFactor (2^j.val) := (by norm_num : (0 : ℝ)≤1).trans
      (logFactor_ge_one (2^j.val) (by positivity))
    have hsq : logFactor (2^j.val)^2≤logFactor T^2 := by nlinarith
    apply hh.trans
    dsimp [A,B,P,H,gamma]
    gcongr
    exact pathLength_nonneg _
  apply (Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hlocal j)).trans
  have hmove := mul_le_mul_of_nonneg_left hsumP hB
  have htime := mul_le_mul_of_nonneg_right hsumH (sq_nonneg tau)
  have hfloor := mul_le_mul_of_nonneg_left hsumR (sq_nonneg D)
  have hsmooth := mul_le_mul_of_nonneg_left (add_le_add htime hfloor)
    (show 0≤gamma*G^2 by positivity)
  have hrewrite : (∑ j : Fin (epochCount T),D^2/H j)=D^2*(∑ j : Fin (epochCount T),1/H j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => by ring)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hrewrite]
  dsimp [A,B,gamma] at *
  ring_nf at hmove hsmooth ⊢
  linarith

end Paper254
#print axioms Paper254.rational_anytime_clipped
