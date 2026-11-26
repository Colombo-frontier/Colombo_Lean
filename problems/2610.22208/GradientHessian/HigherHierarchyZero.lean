import GradientHessian.HigherHierarchyFunctions

/-! Exact values at the physical origin. At every localized height the
origin is outside all supports, so the first child is selected exactly. -/

noncomputable section
namespace GradientHessian.HigherHierarchy

section Node
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nodePorts_zero {R w : ℝ} (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (i : Fin 8) :
    nodePorts w c (0 : Layer F E) i = 0 := by
  apply Localized.port_eq_zero_of_two_mul_le_norm hw
  simpa only [map_zero, PiLp.zero_apply, zero_sub, norm_neg, hc] using
    (show 2*w ≤ R by linarith)

theorem nodeSelf_zero {R w : ℝ} (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) : nodeSelf R w c (0 : Layer F E) = 0 := by
  have hR : 0 ≤ R := by linarith
  have hp (i : Fin 8) : Localized.perturbation R w (c i) (0 : E) = 0 := by
    apply Localized.perturbation_eq_zero_of_three_mul_le_norm hw
    simpa only [zero_sub, norm_neg, hc] using (show 3*w ≤ R by linarith)
  simp [nodeSelf, Localized.potential, hp, Localized.publicPotential_zero hR]

theorem nodeScalar_zero (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (ho : childPort 0 (0 : F) = 0) :
    nodeScalar Q child childPort S R w c (0 : Layer F E) = child 0 0 := by
  simp only [nodeScalar, nodeSelected, FirstHeightSelector.select,
    nodePorts_zero hw hscale c hc, sub_zero, one_mul, zero_mul, add_zero,
    nodeSelf_zero hw hscale c hc, map_zero]
  simp [nodePayload, ho]

end Node

universe u
variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

theorem outgoing_zero {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) : outgoing K t d 0 = 0 := by
  cases t with
  | zero => exact FirstHeight.sourceOutgoing_zero d
  | succ t =>
    exact nodePorts_zero (width_pos m t) (scale_separation m hK t) (centers K d)
      (centers_norm (by linarith) d hd) _

theorem scalar_zero {K : ℝ} (hK : 16 ≤ K) :
    (t : ℕ) → (d : Data Y E H m t) → Valid Y E H m t d →
      scalar K t d 0 = -10*InverseGate.H₀^2
  | 0, d, _ => FirstHeight.sourceNode_zero d
  | t+1, d, hd => by
    rw [scalar, nodeScalar_zero _ _ _ _ (width_pos m t) (scale_separation m hK t)
      (centers K d) (centers_norm (by linarith) d hd)
      (outgoing_zero hK t (d.children 0) (hd.1 0))]
    exact scalar_zero hK t (d.children 0) (hd.1 0)

end GradientHessian.HigherHierarchy
