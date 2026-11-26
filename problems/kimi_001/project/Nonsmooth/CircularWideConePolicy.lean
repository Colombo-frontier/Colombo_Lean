import Nonsmooth.CircularConeSector
import Nonsmooth.PiEstimate

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem circularGridAngle_cos_gap_le (N : ℕ) :
    1 - Real.cos (circularGridAngle N) ≤ circularGridAngle N * Real.sin (circularGridAngle N) := by
  let g : ℝ → ℝ := fun x => x * Real.sin x + Real.cos x - 1
  have hd (x : ℝ) : HasDerivAt g (x * Real.cos x) x := by
    convert! (((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).add
      (Real.hasDerivAt_cos x)).sub_const 1 using 1 <;> (try simp only [id_eq]) <;> ring
  have hc : Continuous g := by dsimp [g]; fun_prop
  have hm : MonotoneOn g (Set.Icc 0 (circularGridAngle N)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hc.continuousOn
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    apply mul_nonneg hx'.1
    apply Real.cos_nonneg_of_mem_Icc
    exact ⟨by linarith [hx'.1, Real.pi_pos], hx'.2.trans (circularGridAngle_le_pi_div_two N)⟩
  have hθ := (circularGridAngle_pos N).le
  have h := hm (Set.left_mem_Icc.mpr hθ) (Set.right_mem_Icc.mpr hθ) hθ
  simp only [g, Real.sin_zero, Real.cos_zero, zero_mul, zero_add, sub_self] at h
  linarith

theorem circularGridAngle_le_dyadic (N : ℕ) : circularGridAngle N ≤ 2 / (2 : ℝ) ^ N := by
  unfold circularGridAngle
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ N)
    (by positivity : (0 : ℝ) < 2 ^ N)).mpr
  have hpi : Real.pi ≤ 4 := by nlinarith [pi_square_le_twenty_one_halves, Real.pi_pos]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (show (0 : ℝ) ≤ 2 ^ N by positivity)]

theorem circular_sector_condition_of_dyadic (N : ℕ) {h t : ℝ}
    (hslope : (2 / (2 : ℝ) ^ N) * |t| ≤ h) :
    (1 - Real.cos (circularGridAngle N)) * |t| ≤ Real.sin (circularGridAngle N) * h := by
  have hθ : circularGridAngle N * |t| ≤ h :=
    (mul_le_mul_of_nonneg_right (circularGridAngle_le_dyadic N) (abs_nonneg t)).trans hslope
  calc
    (1 - Real.cos (circularGridAngle N)) * |t| ≤
      (circularGridAngle N * Real.sin (circularGridAngle N)) * |t| :=
        mul_le_mul_of_nonneg_right (circularGridAngle_cos_gap_le N) (abs_nonneg t)
    _ = Real.sin (circularGridAngle N) * (circularGridAngle N * |t|) := by ring
    _ ≤ Real.sin (circularGridAngle N) * h :=
      mul_le_mul_of_nonneg_left hθ (circularGridAngle_sin_pos N).le

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem circular_grid_wide_cone_policy (o u v : E) (r R : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_ℝ = 0)
    (hr : 0 < r) (hR : ‖o‖ + r ≤ R) (N : ℕ) :
    ∃ p : Policy Unit CyclicPeakState (Feasible E R), p.IsMeasurable ∧
      ∀ f : E → ℝ, ConvexOn ℝ (Metric.closedBall 0 R) f → ∃ j : ℤ,
        (p.result (fun x => f x.val) () (3 * N + 4)).val = circularQueryPoint o u v r N j ∧
        ∀ h t : ℝ, (2 / (2 : ℝ) ^ N) * |t| ≤ h →
          let x := circularQueryPoint o u v r N j
          let z := x + h • circleArc u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N)) +
            t • circleTangent u v (2 * Real.pi * (j : ℝ) / (4 * 2 ^ N))
          ‖z‖ ≤ R → f x ≤ f z := by
  obtain ⟨p, hp, hresult⟩ := circular_grid_local_max_policy o u v r R hu hv huv hr.le hR N
  refine ⟨p, hp, ?_⟩
  intro f hf
  obtain ⟨j, hout, hl, hright⟩ := hresult f
  refine ⟨j, hout, ?_⟩
  intro h t hslope
  dsimp only
  intro hz
  let q : Fin 2 → E := ![circularQueryPoint o u v r N (j - 1),
    circularQueryPoint o u v r N (j + 1)]
  have hq : ∀ i, q i ∈ Metric.closedBall (0 : E) R := by
    intro i
    fin_cases i
    · simpa [q] using circularQueryPoint_feasible hu hv huv hr.le hR N (j - 1)
    · simpa [q] using circularQueryPoint_feasible hu hv huv hr.le hR N (j + 1)
  have hval : ∀ i, f (q i) ≤ f (circularQueryPoint o u v r N j) := by
    intro i
    fin_cases i
    · exact hl
    · exact hright
  exact finiteComparisonCone_value_ge hf q hq hval (by simpa using hz)
    (circular_query_cone_contains_sector o u v hr N j (circular_sector_condition_of_dyadic N hslope))

end
end Nonsmooth
