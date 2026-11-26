import ProjectedGradientRegret254
import FiniteInterface254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem projectedGradient_predictions {d T : ℕ} {D : ℝ} (W : Domain d D)
    (G α : ℝ) (w0 : W.carrier) (f : Fin T → Loss d) (t : Fin T) :
    predictions (onlineProjectedGradient W G α w0) f t =
      projectedGradientTrajectory W G α (extendFinite (fun _ => 0) f) w0 t.val := by
  apply projectedGradientTrajectory_causal
  intro k hk
  have hkT : k < T := Nat.lt_trans hk t.isLt
  simp [extendFinite, hk, hkT, past]

theorem projectedGradient_online_bound {d T : ℕ} {D G η α : ℝ} (W : Domain d D)
    (hT : 0 < T) (hη : 0 < η) (hα : 0 < α) (w0 : W.carrier)
    (f : Fin T → Loss d) (hf : ∀ t, AdmissibleLoss W G η (f t))
    (u : Fin T → W.carrier) :
    regret (onlineProjectedGradient W G α w0) f u ≤
      (D^2+2*D*pathLength u)/(2*α)+α*G^2*T/2 := by
  let ff := extendFinite (fun _ => 0) f
  let uu := extendFinite w0 u
  let zz := projectedGradientTrajectory W G α ff w0
  have heT : T-1+1 = T := by omega
  have hh := dynamic_projected_gradient W hη hα ff zz uu (T-1)
    (by
      intro t ht
      have htT : t < T := by omega
      simpa [ff,extendFinite,htT] using hf ⟨t,htT⟩)
    (by intro t _; rfl)
  rw [heT] at hh
  have hpath : (∑ t ∈ Finset.range (T-1), ‖(uu (t+1)).val-(uu t).val‖) = pathLength u := by
    symm
    simpa only [intervalCharge, Nat.zero_add] using pathLength_extension w0 u
  rw [hpath] at hh
  have hreg : cumulative (fun t => ff t (zz t).val-ff t (uu t).val) T =
      regret (onlineProjectedGradient W G α w0) f u := by
    unfold cumulative regret
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    rw [projectedGradient_predictions]
    simp only [ff,uu,extendFinite_at,zz]
  rw [hreg] at hh
  have hc : (T-1 : ℕ) + (1 : ℝ) = (T : ℝ) := by exact_mod_cast heT
  rwa [hc] at hh

end Paper254
#print axioms Paper254.projectedGradient_online_bound
