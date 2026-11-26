import SphereSmoothingIntegrationByParts
open MeasureTheory Set Metric Function
open scoped NNReal
namespace Task006.SphereSmoothing
noncomputable section

/-- Multiplication by a bounded cutoff needs a bound on f only where the
cutoff is nonzero, and therefore does not strengthen the oracle model. -/
theorem lipschitz_product_of_cutoff {X : Type*} [PseudoMetricSpace X]
    {f η : X → ℝ} {K H C : ℝ≥0} (hf : LipschitzWith K f) (hη : LipschitzWith H η)
    (hηbound : ∀ x, |η x| ≤ 1) (hfbound : ∀ x, η x ≠ 0 → |f x| ≤ C) :
    LipschitzWith (K+C*H) (fun x => f x*η x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  simp only [NNReal.coe_add, NNReal.coe_mul]
  have hdf : |f x-f y| ≤ (K:ℝ)*dist x y := by simpa only [Real.dist_eq] using hf.dist_le_mul x y
  have hdη : |η x-η y| ≤ (H:ℝ)*dist x y := by simpa only [Real.dist_eq] using hη.dist_le_mul x y
  by_cases hx : η x=0
  · by_cases hy : η y=0
    · simp only [hx,hy,mul_zero,sub_self,abs_zero]
      positivity
    · have hb := hfbound y hy
      have heq : |f x*η x-f y*η y| = |f y| * |η x-η y| := by rw [hx]; simp [abs_mul]
      rw [heq]
      calc
        _ ≤ (C:ℝ)*((H:ℝ)*dist x y) := mul_le_mul hb hdη (abs_nonneg _) C.coe_nonneg
        _ ≤ _ := by nlinarith [K.coe_nonneg, dist_nonneg (x := x) (y := y)]
  · have hb := hfbound x hx
    calc
      |f x*η x-f y*η y| = |(f x-f y)*η y+f x*(η x-η y)| := by congr 1; ring
      _ ≤ |f x-f y| * |η y| + |f x| * |η x-η y| := by simpa only [abs_mul] using abs_add_le ((f x-f y)*η y) (f x*(η x-η y))
      _ ≤ ((K:ℝ)*dist x y)*1+(C:ℝ)*((H:ℝ)*dist x y) :=
        add_le_add (mul_le_mul hdf (hηbound y) (abs_nonneg _) (by positivity))
          (mul_le_mul hb hdη (abs_nonneg _) C.coe_nonneg)
      _ = _ := by ring

/-- A radial Lipschitz cutoff equal to one on the rho ball and zero beyond
rho+epsilon; its exact annular derivative gives the spherical boundary term. -/
def radialCutoff {E : Type*} [SeminormedAddCommGroup E] (ρ ε : ℝ) (x : E) : ℝ :=
  max 0 (min 1 ((ρ+ε-‖x‖)/ε))

theorem radialCutoff_nonneg {E : Type*} [SeminormedAddCommGroup E] (ρ ε : ℝ) (x : E) :
    0 ≤ radialCutoff ρ ε x := le_max_left _ _

theorem radialCutoff_le_one {E : Type*} [SeminormedAddCommGroup E] (ρ ε : ℝ) (x : E) :
    radialCutoff ρ ε x ≤ 1 := max_le (by norm_num) (min_le_left _ _)

theorem radialCutoff_eq_one {E : Type*} [SeminormedAddCommGroup E] {ρ ε : ℝ}
    (hε : 0 < ε) {x : E} (hx : ‖x‖ ≤ ρ) : radialCutoff ρ ε x=1 := by
  have hh : 1 ≤ (ρ+ε-‖x‖)/ε := (le_div_iff₀ hε).2 (by linarith)
  simp only [radialCutoff, min_eq_left hh, max_eq_right (by norm_num : (0:ℝ) ≤ 1)]

theorem radialCutoff_eq_zero {E : Type*} [SeminormedAddCommGroup E] {ρ ε : ℝ}
    (hε : 0 < ε) {x : E} (hx : ρ+ε ≤ ‖x‖) : radialCutoff ρ ε x=0 := by
  have hh : (ρ+ε-‖x‖)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  exact max_eq_left (le_trans (min_le_right _ _) hh)

theorem radialCutoff_lipschitz {E : Type*} [SeminormedAddCommGroup E] {ρ ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal ε⁻¹) (radialCutoff (E := E) ρ ε) := by
  have ha : LipschitzWith (Real.toNNReal ε⁻¹) (fun x : E => (ρ+ε-‖x‖)/ε) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← sub_div, show (ρ+ε-‖x‖)-(ρ+ε-‖y‖)=‖y‖-‖x‖ by ring,
      abs_div, abs_of_pos hε, Real.coe_toNNReal _ (inv_pos.2 hε).le]
    calc
      _ ≤ ‖x-y‖/ε := div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using abs_norm_sub_norm_le x y) hε.le
      _ = _ := by rw [dist_eq_norm]; ring
  exact (ha.const_min 1).const_max 0

theorem radialCutoff_hasCompactSupport {d : ℕ} {ρ ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (radialCutoff (E := EuclideanSpace ℝ (Fin d)) ρ ε) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (ρ+ε))
  intro x hx
  have hne : radialCutoff ρ ε x ≠ 0 := hx
  have hnorm : ‖x‖ < ρ+ε := lt_of_not_ge (fun hh => hne (radialCutoff_eq_zero hε hh))
  simpa only [mem_closedBall, dist_zero_right] using hnorm.le

/-- Actual Lipschitz/compactness hypotheses for applying the proved weak
integration-by-parts theorem to the original Lipschitz function times cutoff. -/
theorem radialCutoff_product_regular {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    (∃ K' : ℝ≥0, LipschitzWith K' (fun z => f z*radialCutoff ρ ε z)) ∧
      HasCompactSupport (fun z => f z*radialCutoff ρ ε z) := by
  let C : ℝ := |f 0|+(K:ℝ)*(ρ+ε)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ z, radialCutoff ρ ε z ≠ 0 → |f z| ≤ (Real.toNNReal C : ℝ) := by
    intro z hz
    have hn : ‖z‖ < ρ+ε := lt_of_not_ge (fun hh => hz (radialCutoff_eq_zero hε hh))
    have hd := hf.norm_sub_le z 0
    simp only [Real.norm_eq_abs, sub_zero] at hd
    have hh : |f z| ≤ |f z-f 0|+|f 0| := by
      simpa only [sub_add_cancel] using abs_add_le (f z-f 0) (f 0)
    rw [Real.coe_toNNReal _ hC]
    exact hh.trans (by dsimp [C]; nlinarith [mul_le_mul_of_nonneg_left hn.le K.coe_nonneg])
  have hb (z : EuclideanSpace ℝ (Fin d)) : |radialCutoff ρ ε z| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ ε z)]
    exact radialCutoff_le_one ρ ε z
  exact ⟨⟨_,lipschitz_product_of_cutoff hf (radialCutoff_lipschitz hε) hb hbound⟩,
    (radialCutoff_hasCompactSupport hε).mul_left⟩

end
end Task006.SphereSmoothing
