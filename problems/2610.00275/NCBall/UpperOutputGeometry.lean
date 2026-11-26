import NCBall.UpperProcess
import Mathlib.Analysis.Convex.Combination

/-! # The averaged segment point and its Goldstein certificate -/

noncomputable section
open Set Metric
open scoped BigOperators unitInterval
namespace NCBall

section Average
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_average_mem_convex {S : Set E} (hS : Convex ℝ S) (z : ℕ → E)
    {m : ℕ} (hm : 0 < m) (hz : ∀ t < m, z t ∈ S) :
    (m : ℝ)⁻¹ • (∑ t ∈ Finset.range m, z t) ∈ S := by
  rw [Finset.smul_sum]
  apply hS.sum_mem
  · exact fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg m)
  · simp [ne_of_gt (Nat.cast_pos.mpr hm : (0 : ℝ) < m)]
  · exact fun t ht => hz t (Finset.mem_range.mp ht)

end Average

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def upperOutput (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m : ℕ) : E :=
  (m : ℝ)⁻¹ • ∑ t ∈ Finset.range m, upperLocation D hD α G x₀ r ξ (s + t)

theorem upper_state_shift_bound (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s t : ℕ) :
    ‖(upperState D hD α G x₀ r ξ (s + t)).1 - (upperState D hD α G x₀ r ξ s).1‖ ≤ (t : ℝ) * D := by
  have hb := clipped_path_bound (D := D) (fun j => (upperState D hD α G x₀ r ξ (s + j)).1)
    t (fun j _ => ?_) t le_rfl
  · simpa only [Nat.add_zero] using hb
  · dsimp only
    rw [show s + (j + 1) = s + j + 1 by omega]
    simp only [upperState, add_sub_cancel_left, upper_increment_eq_clipped]
    exact clippedIncrement_norm_le D hD α _ (s + j)

theorem upper_block_endpoint_distance (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m i j : ℕ) (hi : i ≤ m) (hj : j ≤ m) :
    ‖(upperState D hD α G x₀ r ξ (s + i)).1 - (upperState D hD α G x₀ r ξ (s + j)).1‖ ≤ (m : ℝ) * D := by
  by_cases hji : j ≤ i
  · have hb := upper_state_shift_bound D hD α G x₀ r ξ (s + j) (i - j)
    rw [show s + j + (i - j) = s + i by omega] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show i - j ≤ m by omega)) hD)
  · rw [norm_sub_rev]
    have hb := upper_state_shift_bound D hD α G x₀ r ξ (s + i) (j - i)
    rw [show s + i + (j - i) = s + j by omega] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show j - i ≤ m by omega)) hD)

theorem upperLocation_convex_combination (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (t : ℕ) :
    upperLocation D hD α G x₀ r ξ t =
      (1 - (r t : ℝ)) • (upperState D hD α G x₀ r ξ t).1 +
        (r t : ℝ) • (upperState D hD α G x₀ r ξ (t + 1)).1 := by
  simp only [upperLocation, upperState]
  module

theorem upper_block_location_endpoint (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m i j : ℕ) (hi : i < m) (hj : j ≤ m) :
    upperLocation D hD α G x₀ r ξ (s + i) ∈
      closedBall (upperState D hD α G x₀ r ξ (s + j)).1 ((m : ℝ) * D) := by
  rw [upperLocation_convex_combination]
  apply convex_closedBall _ _
  · rw [mem_closedBall, dist_eq_norm]
    exact upper_block_endpoint_distance D hD α G x₀ r ξ s m i j hi.le hj
  · rw [mem_closedBall, dist_eq_norm, show s + i + 1 = s + (i + 1) by omega]
    exact upper_block_endpoint_distance D hD α G x₀ r ξ s m (i + 1) j (by omega) hj
  · exact sub_nonneg.mpr (r (s + i)).property.2
  · exact (r (s + i)).property.1
  · ring

theorem upper_block_location_pair (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m i j : ℕ) (hi : i < m) (hj : j < m) :
    upperLocation D hD α G x₀ r ξ (s + j) ∈
      closedBall (upperLocation D hD α G x₀ r ξ (s + i)) ((m : ℝ) * D) := by
  rw [upperLocation_convex_combination D hD α G x₀ r ξ (s + j)]
  apply convex_closedBall _ _
  · rw [mem_closedBall, dist_comm]
    exact upper_block_location_endpoint D hD α G x₀ r ξ s m i j hi hj.le
  · rw [mem_closedBall, dist_comm, show s + j + 1 = s + (j + 1) by omega]
    exact upper_block_location_endpoint D hD α G x₀ r ξ s m i (j + 1) hi (by omega)
  · exact sub_nonneg.mpr (r (s + j)).property.2
  · exact (r (s + j)).property.1
  · ring

theorem upper_block_location_near_output (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m t : ℕ) (hm : 0 < m) (ht : t < m) :
    upperLocation D hD α G x₀ r ξ (s + t) ∈ closedBall (upperOutput D hD α G x₀ r ξ s m) ((m : ℝ) * D) := by
  rw [mem_closedBall, dist_comm]
  exact finite_average_mem_convex (convex_closedBall _ _)
    (fun j => upperLocation D hD α G x₀ r ξ (s + j)) hm
    (fun j hj => upper_block_location_pair D hD α G x₀ r ξ s m t j ht hj)

theorem upperOutput_in_ball (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m : ℕ) (hm : 0 < m) :
    upperOutput D hD α G x₀ r ξ s m ∈ closedBall x₀ ((s + m : ℕ) * D) := by
  apply finite_average_mem_convex (convex_closedBall _ _) _ hm
  intro t ht
  rw [mem_closedBall, dist_eq_norm]
  exact (upper_sample_location_bound D hD α G x₀ r ξ (s + t)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show s + t + 1 ≤ s + m by omega)) hD)

theorem upperOutput_gradient_certificate (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m : ℕ) (hm : 0 < m) (g : E → E) :
    (m : ℝ)⁻¹ • (∑ t ∈ Finset.range m, g (upperLocation D hD α G x₀ r ξ (s + t))) ∈
      smoothGoldsteinSet g ((m : ℝ) * D) (upperOutput D hD α G x₀ r ξ s m) := by
  apply finite_average_mem_convex convex_closedConvexHull _ hm
  intro t ht
  apply subset_closedConvexHull
  exact mem_image_of_mem g (upper_block_location_near_output D hD α G x₀ r ξ s m t hm ht)

theorem upperOutput_residual_bound (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    (r : ℕ → I) (ξ : ℕ → Ξ) (s m : ℕ) (hm : 0 < m) (g : E → E) :
    smoothGoldsteinResidual g ((m : ℝ) * D) (upperOutput D hD α G x₀ r ξ s m) ≤
      ‖(m : ℝ)⁻¹ • (∑ t ∈ Finset.range m, g (upperLocation D hD α G x₀ r ξ (s + t)))‖ := by
  simpa only [dist_zero_left] using infDist_le_dist_of_mem
    (upperOutput_gradient_certificate D hD α G x₀ r ξ s m hm g) (x := (0 : E))

end NCBall
