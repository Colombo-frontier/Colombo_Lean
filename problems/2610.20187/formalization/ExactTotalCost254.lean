import ExactRoundCost254
import RationalTotalCost254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem exact_live_card_cap (T K t : ℕ) (ht : t≤T+1) :
    (liveExperts T K t).card≤standardLiveCap T K := by
  apply (liveExperts_card T K t).trans
  unfold standardLiveCap
  gcongr

theorem exact_live_list_cap (T K t : ℕ) (ht : t≤T+1) :
    (shortLiveList T K t).length≤standardLiveCap T K := by
  apply (shortLiveList_length T K t).trans
  unfold standardLiveCap
  gcongr

def exactRoundArithmeticBound {d : ℕ} {D : ℝ} {W : Domain d D}
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) :=
  6*d^2+12*d+18+primitive.bound+projection.bound+exponential.bound

theorem countedExactRound_uniform_cost {d T K : ℕ} {D : ℝ} (W : Domain d D)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ) (S : SparseMasterState W T K)
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (K+1)→ℝ) (hq : ∀ k,0<q k)
    (t : Fin T) (query : Coordinates d→Coordinates d) :
    (countedExactRound W primitive projection exponential gradientCost S lam hlam q hq t query).2≤
      standardLiveCap T K*exactRoundArithmeticBound primitive projection exponential+gradientCost+5 := by
  apply (countedExactRound_cost W primitive projection exponential gradientCost S lam hlam q hq t query).trans
  have h1 := Nat.mul_le_mul_right (6*d^2+7*d+3+primitive.bound+projection.bound)
    (exact_live_list_cap T K (t.val+1) (by omega))
  have h2 := Nat.mul_le_mul_right (5*d+exponential.bound+9)
    (exact_live_card_cap T K (t.val+1) (by omega))
  have h3 := Nat.mul_le_mul_left 6 (exact_live_card_cap T K (t.val+2) (by omega))
  unfold exactRoundArithmeticBound
  nlinarith

/-- Complete round arithmetic: prediction, one queried gradient, all
surrogates, exponential/share master, and all actual history updates. -/
theorem exact_curved_total_cost {d T : ℕ} {D : ℝ} (W : Domain d D) (hT : 0<T)
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (gradientCost : ℕ)
    (states : Fin T→SparseMasterState W T (scaleCount T))
    (lam : ℝ) (hlam : 0≤lam) (q : Fin (scaleCount T+1)→ℝ) (hq : ∀ k,0<q k)
    (query : Fin T→Coordinates d→Coordinates d) :
    (∑ t : Fin T,
      ((countedExactRound W primitive projection exponential gradientCost (states t)
        lam hlam q hq t (query t)).2:ℝ))≤
      40*T*logFactor T^2*exactRoundArithmeticBound primitive projection exponential+
        T*(gradientCost+5) := by
  have hh : (∑ t : Fin T,(countedExactRound W primitive projection exponential gradientCost
      (states t) lam hlam q hq t (query t)).2)≤
      T*(standardLiveCap T (scaleCount T)*exactRoundArithmeticBound primitive projection exponential+
        gradientCost+5) := by
    calc
      _≤∑ _t : Fin T,(standardLiveCap T (scaleCount T)*
          exactRoundArithmeticBound primitive projection exponential+gradientCost+5) :=
        Finset.sum_le_sum (fun t ht=>countedExactRound_uniform_cost W primitive projection
          exponential gradientCost (states t) lam hlam q hq t (query t))
      _=_ := by simp
  have hr : (∑ t : Fin T,
      ((countedExactRound W primitive projection exponential gradientCost (states t)
        lam hlam q hq t (query t)).2:ℝ))≤
      T*((standardLiveCap T (scaleCount T):ℝ)*
        exactRoundArithmeticBound primitive projection exponential+gradientCost+5) := by
    exact_mod_cast hh
  have hb := mul_le_mul_of_nonneg_right (standardLiveCap_log_bound T hT)
    (show (0:ℝ)≤exactRoundArithmeticBound primitive projection exponential by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤T by positivity)]

theorem exact_dense_arithmetic_bound {d : ℕ} (hd : 0<d) {D : ℝ} {W : Domain d D}
    (spectral : ExactSpectralPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (c : ℕ) (hc : spectral.bound≤c*d^3) :
    exactRoundArithmeticBound (denseRankOneFloorPrimitive spectral) projection exponential≤
      (c+44)*d^3+projection.bound+exponential.bound := by
  unfold exactRoundArithmeticBound denseRankOneFloorPrimitive
  have hd2 : d≤d^2 := by nlinarith
  have hd3 : d^2≤d^3 := by nlinarith [Nat.mul_le_mul_right (d^2) hd]
  nlinarith

theorem exact_quadratic_arithmetic_bound {d : ℕ} (hd : 0<d) {D : ℝ} {W : Domain d D}
    (primitive : ExactRankOneFloorPrimitive d) (projection : ExactProjectionPrimitive W)
    (exponential : ExactExpPrimitive) (c : ℕ) (hc : primitive.bound≤c*d^2) :
    exactRoundArithmeticBound primitive projection exponential≤
      (c+36)*d^2+projection.bound+exponential.bound := by
  unfold exactRoundArithmeticBound
  have hd2 : d≤d^2 := by nlinarith
  nlinarith

end Paper254
#print axioms Paper254.exact_curved_total_cost
#print axioms Paper254.exact_dense_arithmetic_bound
#print axioms Paper254.exact_quadratic_arithmetic_bound
