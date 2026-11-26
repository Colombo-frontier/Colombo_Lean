import GradientHessian.FirstHeightFunctions

/-! Exact energy accounting for the first hierarchy height, before the
literal capped-leaf estimates are substituted. No node estimates are assumed. -/

noncomputable section
namespace GradientHessian.FirstHeight
open EuclideanRegisters InnerCoordinates

def amplitude (b : ℕ) (S R : ℝ) : ℝ := b * (S + 112 * R)

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem incoming_product_bounds (childPort : Fin b → F → ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b)
    (ho : childPort i (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1) :
    Inner.input (v i) (tasks F E b (k + 2) Z i) *
      childPort i (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 56 := by
  have hB := Inner.input_bounds (v i) (tasks F E b (k + 2) Z i)
  exact ⟨mul_nonneg hB.1 ho.1,
    (mul_le_mul_of_nonneg_left ho.2 hB.1).trans (by simpa using hB.2)⟩

theorem payload_interval (Q : F → ℝ) (child childPort : Fin b → F → ℝ) {A₀ : ℝ}
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b)
    (hc : -A₀ ≤ child i (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ∧
      child i (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ≤ 0)
    (ho : childPort i (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1) :
    -((i.val : ℝ) + 1) * (A₀ + 56) ≤ payload Q child childPort (A₀ + 56) v Z i ∧
      payload Q child childPort (A₀ + 56) v Z i ≤ -(i.val : ℝ) * (A₀ + 56) := by
  have hB := incoming_product_bounds childPort v Z i ho
  unfold payload
  constructor <;> nlinarith [hB.1, hB.2, hc.1, hc.2]

theorem residual_nonpos (Q : F → ℝ) (child childPort : Fin b → F → ℝ) {S : ℝ} (hS : 0 ≤ S)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k)
    (hc : ∀ i, child i (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ≤ 0)
    (ho : ∀ i, childPort i (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1) :
    residual Q child childPort S v Z ≤ 0 := by
  rw [residual_eq]
  have hsel : selected Q child childPort S v Z ≤ 0 := by
    apply FirstHeightSelector.select_le b _ _ _ 0 (Inner.ports_bounds v Z)
    · intro i
      have hB := (incoming_product_bounds childPort v Z i (ho i)).1
      have hidx := mul_nonneg (Nat.cast_nonneg i.val) hS
      unfold payload
      linarith [hc i]
    · simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg b) hS)
  linarith [(Inner.sumResidual_bounds v Z).2]

theorem residual_bounds (Q : F → ℝ) (child childPort : Fin b → F → ℝ) {A₀ : ℝ} (hA : 0 ≤ A₀)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k)
    (hc : ∀ i, -A₀ ≤ child i (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ∧
      child i (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ≤ 0)
    (ho : ∀ i, childPort i (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1) :
    -amplitude b (A₀ + 56) (Inner.lastRadius k) ≤ residual Q child childPort (A₀ + 56) v Z ∧
      residual Q child childPort (A₀ + 56) v Z ≤ 0 := by
  have hS : 0 ≤ A₀ + 56 := by linarith
  refine ⟨?_, residual_nonpos Q child childPort hS v Z (fun i => (hc i).2) ho⟩
  have hsel : -(b : ℝ) * (A₀ + 56) ≤ selected Q child childPort (A₀ + 56) v Z := by
    apply FirstHeightSelector.le_select b _ _ _ _ (Inner.ports_bounds v Z) _ le_rfl
    intro i
    have hidx : (i.val : ℝ) + 1 ≤ b := by exact_mod_cast i.isLt
    have hi := mul_le_mul_of_nonneg_right hidx hS
    linarith [(payload_interval Q child childPort v Z i (hc i) (ho i)).1]
  rw [residual_eq]
  unfold amplitude
  nlinarith [(Inner.sumResidual_bounds v Z).1]

theorem selfSum_eq (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) :
    Inner.selfSum v Z = Inner.publicQuadratic b k Z + Inner.sumResidual v Z := by
  have h := Inner.residual_eq_sumResidual_sub (fun _ : Fin b => (0 : F))
    (fun _ : Fin b => (0 : F)) v Z
  unfold Inner.residual at h
  linarith

/-- The common positive lower energy is kept throughout the convex selector;
only one child loss is charged, not one loss per child. -/
theorem global_energy (Q : F → ℝ) (child childPort : Fin b → F → ℝ) {S C H : ℝ}
    (hS : 56 ≤ S) (hC : 0 ≤ C) (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k)
    (hQ : H ≤ Q (numerical F E b (k + 2) Z))
    (hc : ∀ i, H - C ≤ child i (numerical F E b (k + 2) Z))
    (ho : ∀ i, childPort i (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1) :
    H + Inner.publicQuadratic b k Z - amplitude b S (Inner.lastRadius k) - C ≤
      node Q child childPort S v Z := by
  have hS0 : 0 ≤ S := by linarith
  have hsel : H - Q (numerical F E b (k + 2) Z) - C - b * S ≤
      selected Q child childPort S v Z := by
    apply FirstHeightSelector.le_select b _ _ _ _ (Inner.ports_bounds v Z)
    · intro i
      have hB := (incoming_product_bounds childPort v Z i (ho i)).2
      have hidx : (i.val : ℝ) + 1 ≤ b := by exact_mod_cast i.isLt
      have hi := mul_le_mul_of_nonneg_right hidx hS0
      unfold payload
      nlinarith [hc i]
    · linarith
  rw [node, selfSum_eq]
  unfold amplitude
  nlinarith [(Inner.sumResidual_bounds v Z).1]

end GradientHessian.FirstHeight
