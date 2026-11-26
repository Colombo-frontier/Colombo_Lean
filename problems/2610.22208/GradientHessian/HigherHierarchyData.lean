import GradientHessian.HigherHierarchySpace
import GradientHessian.HigherHierarchyScales

/-! Coefficient trees for the literal hierarchy. Child labels belong to
data only: all eight children are functions on the same physical prefix. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

structure StepData (D E : Type u) where
  children : Fin 8 → D
  directions : Fin 8 → E

variable (Y E : Type u) (H : ℕ → Type u) (m : ℕ)
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Data : ℕ → Type u
  | 0 => FirstHeight.Data Y E m
  | t+1 => StepData (Data t) (H t)

variable [CompleteSpace Y]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

/-- These are coefficient assumptions only, recursively inherited from
the actual matrix/readout leaf data and unit parent directions. -/
def Valid : (t : ℕ) → Data Y E H m t → Prop
  | 0, d => FirstHeight.Valid d
  | t+1, d => (∀ i, Valid t (d.children i)) ∧ ∀ i, ‖d.directions i‖ = 1

variable {Y E H m}

def centers {t : ℕ} (K : ℝ) (d : Data Y E H m (t+1)) (i : Fin 8) : H t :=
  radius m K t • d.directions i

theorem centers_norm {t : ℕ} {K : ℝ} (hK : 0 ≤ K) (d : Data Y E H m (t+1))
    (hd : Valid Y E H m (t+1) d) (i : Fin 8) : ‖centers K d i‖ = radius m K t := by
  have hr : 0 ≤ radius m K t :=
    mul_nonneg (mul_nonneg hK (baseRadius_pos m).le) (by positivity)
  rw [centers, norm_smul, hd.2 i, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]

end GradientHessian.HigherHierarchy
