import GradientHessian.HigherHierarchyActivationNode

/-! Activation of the literal hierarchy at every finite height. Numerical
localization and every child activation premise are discharged here. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def immediatePorts (K : ℝ) : (t : ℕ) → Data Y E H m t → Space Y E H m t → Fin 8 → ℝ
  | 0, d, Z => Inner.ports d.outerDirections Z
  | t+1, d, Z => nodePorts (width m t) (centers K d) Z

theorem outgoing_eq_last (K : ℝ) (t : ℕ) (d : Data Y E H m t) (Z : Space Y E H m t) :
    outgoing K t d Z = immediatePorts K t d Z (Fin.last 7) := by
  cases t <;> rfl

theorem immediatePorts_bounds (K : ℝ) (t : ℕ) (d : Data Y E H m t) (Z : Space Y E H m t) (i : Fin 8) :
    immediatePorts K t d Z i ∈ Set.Icc (0:ℝ) 1 := by
  cases t with
  | zero => exact Inner.ports_bounds d.outerDirections Z i
  | succ t => exact nodePorts_bounds _ _ _ _

variable [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)]

/-- Assertion (iii) of `lem:hierarchy-analytic`, for the actual recursive
scalar and every nonnegative outgoing coefficient. -/
theorem activation {K : ℝ} (hK : 16 ≤ K) :
    ∀ t (d : Data Y E H m t), Valid Y E H m t d → ∀ l, 0 ≤ l → ∀ Z : Space Y E H m t,
      ‖gradient (driven K t d l) Z‖ ≤ 1 → ∀ i, immediatePorts K t d Z i = 1 := by
  intro t
  induction t with
  | zero =>
    intro d hd l hl Z hg
    exact FirstHeight.source_activation d hd hl Z hg
  | succ t ih =>
    intro d hd l hl Z hg
    have hK0 : 0 < K := by linarith
    have hZ := driven_localization hK0 (t+1) d hd l Z hg
    apply node_activation_at_bounded_lower (baseline K t) (fun i => scalar K t (d.children i))
      (fun i => outgoing K t (d.children i)) (energy_pos m hK0.le t).le
      (width_pos m t) (scale_separation m hK t) (centers K d) (centers_norm hK0.le d hd) hl
      (baseline_contDiff hK0 t) (fun i => scalar_contDiff hK0 t (d.children i))
      (fun i => outgoing_contDiff hK0 t (d.children i)) ?_ Z ?_
      (fun i => outgoing_bounds K t (d.children i) (lower _ _ Z)) hg
    · intro i a ha x hx
      change outgoing K t (d.children i) x = 1
      rw [outgoing_eq_last]
      exact ih (d.children i) (hd.1 i) a ha x hx (Fin.last 7)
    · intro i
      exact residual_bounded hK t (d.children i) (hd.1 i) (lower _ _ Z) hZ

theorem activation_outgoing_one {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) {l : ℝ} (hl : 0 ≤ l) (Z : Space Y E H m t)
    (hg : ‖gradient (driven K t d l) Z‖ ≤ 1) : outgoing K t d Z = 1 := by
  rw [outgoing_eq_last]
  exact activation hK t d hd l hl Z hg (Fin.last 7)

end GradientHessian.HigherHierarchy
