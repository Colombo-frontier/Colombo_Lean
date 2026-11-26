import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas

/-! Explicit scalar truncation preserving the Lipschitz constant. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Filter
open scoped Topology

def scalarClip (R x : ℝ) : ℝ := max (min x R) (-R)

theorem scalarClip_lipschitz (R : ℝ) : LipschitzWith 1 (scalarClip R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  exact (norm_sup_sub_sup_le_norm (x ⊓ R) (y ⊓ R) (-R)).trans
    (norm_inf_sub_inf_le_norm x y R)

theorem scalarClip_bounds {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    -R ≤ scalarClip R x ∧ scalarClip R x ≤ R :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩

theorem scalarClip_eq_self {R x : ℝ} (hx : -R ≤ x ∧ x ≤ R) : scalarClip R x = x := by
  rw [scalarClip, min_eq_left hx.2, max_eq_left hx.1]

theorem scalarClip_zero {R : ℝ} (hR : 0 ≤ R) : scalarClip R 0 = 0 :=
  scalarClip_eq_self ⟨by linarith, hR⟩

theorem scalarClip_norm_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : ‖scalarClip R x‖ ≤ R :=
  abs_le.mpr (scalarClip_bounds hR x)

theorem scalarClip_norm_le_input {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : ‖scalarClip R x‖ ≤ ‖x‖ := by
  have h := (scalarClip_lipschitz R).dist_le_mul x 0
  simpa only [scalarClip_zero hR, dist_zero_right, NNReal.coe_one, one_mul] using h

theorem scalarClip_eventually_eq (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, scalarClip (n + 1) x = x := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hx : ‖x‖ ≤ (n : ℝ) + 1 := by linarith
  exact scalarClip_eq_self (abs_le.mp hx)

theorem scalarClip_tendsto (x : ℝ) : Tendsto (fun n : ℕ => scalarClip (n + 1) x) atTop (𝓝 x) :=
  tendsto_const_nhds.congr' ((scalarClip_eventually_eq x).mono (fun _ h => h.symm))

end GradientHessian.GaussianConcentration
