import ProjectedGradient254

noncomputable section
open scoped BigOperators
namespace Paper254

def projectedGradientTrajectory {d : ℕ} {D : ℝ} (W : Domain d D)
    (G α : ℝ) (f : ℕ → Loss d) (z₀ : W.carrier) : ℕ → W.carrier
  | 0 => z₀
  | n+1 => projectedGradientStep W G α (f n) (projectedGradientTrajectory W G α f z₀ n)

theorem projectedGradientTrajectory_causal {d : ℕ} {D : ℝ} (W : Domain d D)
    (G α : ℝ) (f g : ℕ → Loss d) (z₀ : W.carrier) (n : ℕ)
    (h : ∀ t < n, f t = g t) :
    projectedGradientTrajectory W G α f z₀ n = projectedGradientTrajectory W G α g z₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [projectedGradientTrajectory]
    rw [h n (Nat.lt_succ_self n), ih (fun t ht => h t (Nat.lt.step ht))]

def onlineProjectedGradient {d T : ℕ} {D : ℝ} (W : Domain d D)
    (G α : ℝ) (z₀ : W.carrier) : OnlineLearner W T :=
  fun t history => projectedGradientTrajectory W G α
    (fun k => if hk : k < t.val then history ⟨k,hk⟩ else fun _ => 0) z₀ t.val

/-- Full dynamic projected-gradient potential telescope over n+1 rounds,
including exactly n internal comparator movements. -/
theorem projectedGradient_potential_bound {d : ℕ} {D G η α : ℝ} (W : Domain d D)
    (hη : 0 < η) (hα : 0 < α) (f : ℕ → Loss d) (z u : ℕ → W.carrier) (n : ℕ)
    (hf : ∀ t ≤ n, AdmissibleLoss W G η (f t))
    (hz : ∀ t ≤ n, z (t+1) = projectedGradientStep W G α (f t) (z t)) :
    2*α*cumulative (fun t => f t (z t).val-f t (u t).val) (n+1) ≤
      ‖(z 0).val-(u 0).val‖^2-‖(z (n+1)).val-(u n).val‖^2 +
      2*D*(∑ t ∈ Finset.range n, ‖(u (t+1)).val-(u t).val‖) + α^2*G^2*(n+1) := by
  induction n with
  | zero =>
    have hs := projectedGradient_one_step W hη hα (hf 0 (le_refl _)) (z 0) (u 0)
    rw [← hz 0 (le_refl _)] at hs
    simpa [cumulative] using hs
  | succ n ih =>
    have hp := ih (fun t ht => hf t (Nat.le_step ht)) (fun t ht => hz t (Nat.le_step ht))
    have hs := projectedGradient_one_step W hη hα (hf (n+1) (le_refl _)) (z (n+1)) (u (n+1))
    rw [← hz (n+1) (le_refl _)] at hs
    have hm := comparator_squared_distance_movement W (z (n+1)) (u n) (u (n+1))
    rw [cumulative_succ, Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one] at *
    nlinarith

/-- Lemma B.13 with every term explicit. Indexing is 0,...,n, so the horizon
is n+1 and the variation sum contains n jumps. -/
theorem dynamic_projected_gradient {d : ℕ} {D G η α : ℝ} (W : Domain d D)
    (hη : 0 < η) (hα : 0 < α) (f : ℕ → Loss d) (z u : ℕ → W.carrier) (n : ℕ)
    (hf : ∀ t ≤ n, AdmissibleLoss W G η (f t))
    (hz : ∀ t ≤ n, z (t+1) = projectedGradientStep W G α (f t) (z t)) :
    cumulative (fun t => f t (z t).val-f t (u t).val) (n+1) ≤
      (D^2+2*D*(∑ t ∈ Finset.range n, ‖(u (t+1)).val-(u t).val‖))/(2*α) +
        α*G^2*(n+1)/2 := by
  have hp := projectedGradient_potential_bound W hη hα f z u n hf hz
  have hd := W.diameter (z 0).val (z 0).property (u 0).val (u 0).property
  have hd2 : ‖(z 0).val-(u 0).val‖^2 ≤ D^2 := by
    nlinarith [norm_nonneg ((z 0).val-(u 0).val)]
  have hb : 2*α*cumulative (fun t => f t (z t).val-f t (u t).val) (n+1) ≤
      D^2+2*D*(∑ t ∈ Finset.range n, ‖(u (t+1)).val-(u t).val‖)+α^2*G^2*(n+1) := by
    nlinarith [sq_nonneg ‖(z (n+1)).val-(u n).val‖]
  have hdiv : cumulative (fun t => f t (z t).val-f t (u t).val) (n+1) ≤
      (D^2+2*D*(∑ t ∈ Finset.range n, ‖(u (t+1)).val-(u t).val‖)+α^2*G^2*(n+1))/(2*α) := by
    apply (le_div_iff₀ (show 0 < 2*α by positivity)).mpr
    nlinarith [hb]
  convert hdiv using 1
  field_simp

end Paper254
#print axioms Paper254.projectedGradientTrajectory_causal
#print axioms Paper254.dynamic_projected_gradient
