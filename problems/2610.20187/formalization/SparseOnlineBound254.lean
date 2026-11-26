import SparseFixedScale254
import FiniteInterface254

noncomputable section
namespace Paper254

/-- Full fixed-scale guarantee for an actual proper, causal learner.
The learner is chosen independently of the losses and comparator and
simultaneously competes at every scale in its supplied finite grid. -/
theorem sparse_online_fixed_scale {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k)
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) (k : Fin (K+1)) (L : ℕ) (hL : 1 ≤ L) (hpow : T < 2^L) :
    let lam := curvature D G η/2
    let a := masterOverhead T K lam
    let B := birthBudget d D (q k)
    let H := restartThreshold L a B lam
    let V := variationThreshold L a B lam (q k)
    regret (sparseOnlineLearner W hD hG hη w0 q hq) f u ≤
      (H/64)*(1+pathLength u/V)+curvature D G η*G^2*T*(q k)/2 := by
  let fExt := extendFinite (fun _ => 0) f
  let uExt := extendFinite w0 u
  have hfExt : ∀ t < T, AdmissibleLoss W G η (fExt t) := by
    intro t ht
    simpa only [fExt, extendFinite, dif_pos ht] using hf ⟨t,ht⟩
  have hh := sparse_fixed_scale (T := T) W hD hG hη w0 q hq fExt hfExt k uExt L hL hpow
  have hreg := sparseOnline_regret W hD hG hη w0 q hq f u
  have hpath := pathLength_extension w0 u
  change pathLength u = intervalCharge (fun t => ‖(uExt (t+1)).val-(uExt t).val‖) 0 (T-1) at hpath
  rw [← hpath] at hh
  rw [← hreg] at hh
  exact hh

end Paper254
#print axioms Paper254.sparse_online_fixed_scale
