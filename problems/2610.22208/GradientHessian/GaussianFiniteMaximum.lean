import GradientHessian.GaussianSoftMaximum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual finite maximum is Lipschitz, and the soft maximum
approximates it with the exact deterministic logarithmic error. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open Filter
open scoped BigOperators NNReal Topology

variable {I : Type*} [Fintype I] [Nonempty I]

def finiteMaximum (x : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

theorem finiteMaximum_attained (x : I → ℝ) : ∃ i, finiteMaximum x = x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty x
  exact ⟨i, hi⟩

theorem le_finiteMaximum (x : I → ℝ) (i : I) : x i ≤ finiteMaximum x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem finiteMaximum_le {x : I → ℝ} {a : ℝ} (h : ∀ i, x i ≤ a) : finiteMaximum x ≤ a :=
  (Finset.sup'_le_iff Finset.univ_nonempty x).mpr (fun i _ => h i)

theorem finiteMaximum_lipschitz : LipschitzWith 1 (finiteMaximum (I := I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one]
  rw [dist_eq_norm, Real.norm_eq_abs, one_mul, dist_eq_norm]
  have hd (u v : I → ℝ) : finiteMaximum u - finiteMaximum v ≤ ‖u - v‖ := by
    obtain ⟨i, hi⟩ := finiteMaximum_attained u
    have hn : u i - v i ≤ ‖u - v‖ :=
      (le_abs_self _).trans (norm_le_pi_norm (u-v) i)
    have hv := le_finiteMaximum v i
    rw [hi]
    linarith
  apply abs_le.mpr
  constructor
  · have h := hd y x
    rw [norm_sub_rev] at h
    linarith
  · exact hd x y

theorem finiteMaximum_le_softMaximum {β : ℝ} (hβ : 0 < β) (x : I → ℝ) :
    finiteMaximum x ≤ softMaximum β x := by
  apply finiteMaximum_le
  intro i
  have hs : Real.exp (β * x i) ≤ softPartition β x := by
    unfold softPartition
    exact Finset.single_le_sum (fun j _ => (Real.exp_pos (β * x j)).le) (Finset.mem_univ i)
  have hl := Real.log_le_log (Real.exp_pos (β * x i)) hs
  rw [Real.log_exp] at hl
  exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hl)

theorem softMaximum_le_finiteMaximum {β : ℝ} (hβ : 0 < β) (x : I → ℝ) :
    softMaximum β x ≤ finiteMaximum x + Real.log (Fintype.card I) / β := by
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hs : softPartition β x ≤ (Fintype.card I : ℝ) * Real.exp (β * finiteMaximum x) := by
    calc
      _ ≤ ∑ _i : I, Real.exp (β * finiteMaximum x) :=
        Finset.sum_le_sum (fun i _ => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (le_finiteMaximum x i) hβ.le))
      _ = _ := by simp
  have hl := Real.log_le_log (softPartition_pos β x) hs
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  apply (div_le_iff₀ hβ).mpr
  dsimp [softMaximum]
  have he : (finiteMaximum x + Real.log (Fintype.card I) / β) * β =
      Real.log (Fintype.card I) + β * finiteMaximum x := by field_simp; ring
  rwa [he]

theorem softMaximum_error {β : ℝ} (hβ : 0 < β) (x : I → ℝ) :
    dist (softMaximum β x) (finiteMaximum x) ≤ Real.log (Fintype.card I) / β := by
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (finiteMaximum_le_softMaximum hβ x))]
  linarith [softMaximum_le_finiteMaximum hβ x]

end GradientHessian.GaussianConcentration
