import SparseLowVariation254

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Paper254

theorem birthBudget_positive (d : ℕ) (D q : ℝ) (hD : 0 < D) (hq : 0 < q) :
    0 < birthBudget d D q := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hq (sq_pos_of_pos hD))
  have hm := mul_nonneg (Nat.cast_nonneg d (α := ℝ))
    (show 0 ≤ q/D^2-1-Real.log (q/D^2) by linarith)
  unfold birthBudget
  linarith

section Trajectory
variable {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
  (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
  (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d)

local notation "S" => sparseTrajectory (T := T) W hD hG hη w0 q hq f
local notation "γ" => curvature D G η
local notation "lam" => curvature D G η/2
local notation "a₀" => masterOverhead T K lam

theorem actual_loss_surrogate_bound (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (k : Fin (K+1)) (u : ℕ → W.carrier) (t : ℕ) (ht : t < T) :
    f t (S t).prediction.val-f t (u t).val ≤
      actualComparatorDifference (T := T) W hD hG hη w0 q hq f k u t+γ*G^2*(q k)/2 := by
  let g := actualSparseGradient (T := T) W hD hG hη w0 q hq f t
  let w := (S t).prediction
  have hg := selectedGradient_spec W (hf t ht) w
  have hs := surrogate_domination W hD hG hη (hf t ht).expConcave hg.1 hg.2 w.property (u t).property
  have he : actualComparatorDifference (T := T) W hD hG hη w0 q hq f k u t =
      -rankOneSurrogate γ g w.val (u t).val-γ*(q k)*((g : Coordinates d) ⬝ᵥ (g : Coordinates d))/2 := by
    change rankOneSurrogate γ g w.val w.val-
      (coordinateSurrogate γ g w.val (u t).val+γ*(q k)*((g : Coordinates d) ⬝ᵥ (g : Coordinates d))/2) = _
    rw [coordinate_surrogate_eq]
    have hz : rankOneSurrogate γ g w.val w.val = 0 := by simp [rankOneSurrogate]
    rw [hz]
    ring
  have hgquad : (g : Coordinates d) ⬝ᵥ (g : Coordinates d) = ‖g‖^2 := by
    rw [coordinate_inner, real_inner_self_eq_norm_sq]
  have hgnorm : ‖g‖ ≤ G := hg.2
  have hg2 : ‖g‖^2 ≤ G^2 := by nlinarith [hgnorm, norm_nonneg g]
  have hsm := mul_le_mul_of_nonneg_left hg2
    (mul_nonneg (curvature_pos D G η hD hG hη).le (hq k).le)
  rw [he, hgquad]
  change f t w.val-f t (u t).val ≤ -rankOneSurrogate γ g w.val (u t).val at hs
  nlinarith

theorem sparse_fixed_scale (hf : ∀ t < T, AdmissibleLoss W G η (f t))
    (k : Fin (K+1)) (u : ℕ → W.carrier) (L : ℕ) (hL : 1 ≤ L) (hpow : T < 2^L) :
    intervalCharge (fun t => f t (S t).prediction.val-f t (u t).val) 0 T ≤
      (restartThreshold L a₀ (birthBudget d D (q k)) lam/64)*
        (1+intervalCharge (fun t => ‖(u (t+1)).val-(u t).val‖) 0 (T-1)/
          variationThreshold L a₀ (birthBudget d D (q k)) lam (q k))+
      γ*G^2*T*(q k)/2 := by
  let B := birthBudget d D (q k)
  let H := restartThreshold L a₀ B lam
  let V := variationThreshold L a₀ B lam (q k)
  let r := actualComparatorDifference (T := T) W hD hG hη w0 q hq f k u
  let delta := fun t => ‖(u (t+1)).val-(u t).val‖
  have hlam : 0 < lam := div_pos (curvature_pos D G η hD hG hη) (by norm_num)
  have ha := masterOverhead_nonneg T K lam hlam
  have hB : 0 < B := birthBudget_positive d D (q k) hD (hq k)
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hH : 0 < H := by dsimp [H, restartThreshold]; positivity
  have hV : 0 < V := by
    have hEnergy : 0 < B+lam*H := add_pos_of_pos_of_nonneg hB (mul_nonneg hlam.le hH.le)
    change 0 < Real.sqrt (q k)*Real.sqrt (B+lam*H)/(512*L)
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (hq k)) (Real.sqrt_pos.mpr hEnergy)) (by positivity)
  have hlocal : ∀ a n, 0 < n → a+n ≤ T → intervalCharge delta a (n-1) ≤ V →
      intervalCharge r a n ≤ H/64 := by
    intro a n hn hend hvar
    exact sparse_low_variation W hD hG hη w0 q hq f hf k u L hL hpow a n hn hend hvar
  have hh := variation_partition_regret r delta T (H/64) V (fun _ => norm_nonneg _)
    (by positivity) hV hlocal 0 T (by omega)
  have hsum : intervalCharge (fun t => f t (S t).prediction.val-f t (u t).val) 0 T ≤
      intervalCharge r 0 T+γ*G^2*T*(q k)/2 := by
    have hp := Finset.sum_le_sum (s := Finset.range T)
      (fun t ht => actual_loss_surrogate_bound W hD hG hη w0 q hq f hf k u t (Finset.mem_range.mp ht))
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hp
    simp only [intervalCharge, Nat.zero_add]
    convert hp using 1 <;> ring
  change _ ≤ (H/64)*(1+intervalCharge delta 0 (T-1)/V)+γ*G^2*T*(q k)/2
  linarith

end Trajectory
end Paper254
#print axioms Paper254.sparse_fixed_scale
