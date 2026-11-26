import GradientHessian.HigherHierarchyFunctions

/-! Flattening coefficients and convex weights into finite leaf slots.
The slot product labels data only, while all leaves share one coordinate. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

def LeafSlot : ℕ → Type
  | 0 => Fin 8
  | t+1 => Fin 8 × LeafSlot t

def leafSlotFintype : (t : ℕ) → Fintype (LeafSlot t)
  | 0 => inferInstanceAs (Fintype (Fin 8))
  | t+1 => by
    letI := leafSlotFintype t
    exact inferInstanceAs (Fintype (Fin 8 × LeafSlot t))
attribute [instance] leafSlotFintype

section Node
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def nodeWeights (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) : Fin 8 → ℝ :=
  InnerSelector.weight (nodePorts w c Z)
def nodeTerminal (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) : ℝ := ∏ i, nodePorts w c Z i

theorem nodeWeights_nonneg (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) (i : Fin 8) :
    0 ≤ nodeWeights w c Z i :=
  SelectorPayloadBounds.finite_weight_nonneg _ (nodePorts_bounds w c Z) i
theorem nodeTerminal_nonneg (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) :
    0 ≤ nodeTerminal w c Z := Finset.prod_nonneg (fun i _ => (nodePorts_bounds w c Z i).1)
theorem nodeWeights_partition (w : ℝ) (c : Fin 8 → G) (Z : Layer F G) :
    nodeTerminal w c Z + ∑ i, nodeWeights w c Z i = 1 := by
  rw [add_comm]
  exact SelectorPayloadBounds.finite_weight_partition 8 _
end Node

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

structure LeafCoefficients (Y E : Type u) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (m : ℕ) where
  A : Y →L[ℝ] Y
  b : Fin (m+1) → Y
  a : Fin (m+1) → Y
  v : Fin (m+1) → Fin (Inner.absoluteDepth+2) → E

def leafData : (t : ℕ) → Data Y E H m t → LeafSlot t → LeafCoefficients Y E m
  | 0, d, i => ⟨d.A i, d.b i, d.a i, d.innerDirections i⟩
  | t+1, d, i => leafData t (d.children i.1) i.2

def leafWeights (K : ℝ) : (t : ℕ) → Data Y E H m t → Space Y E H m t → LeafSlot t → ℝ
  | 0, d, Z => FirstHeight.sourceWeights d Z
  | t+1, d, Z => fun a => nodeWeights (width m t) (centers K d) Z a.1 *
      leafWeights K t (d.children a.1) (lower _ _ Z) a.2

def resetWeight (K : ℝ) : (t : ℕ) → Data Y E H m t → Space Y E H m t → ℝ
  | 0, d, Z => FirstHeight.sourceTerminal d Z
  | t+1, d, Z => nodeTerminal (width m t) (centers K d) Z +
      ∑ i, nodeWeights (width m t) (centers K d) Z i * resetWeight K t (d.children i) (lower _ _ Z)

theorem leafWeights_nonneg (K : ℝ) : ∀ t (d : Data Y E H m t) (Z : Space Y E H m t) (i : LeafSlot t),
    0 ≤ leafWeights K t d Z i
  | 0, d, Z, i => FirstHeight.sourceWeights_nonneg d Z i
  | t+1, d, Z, i => mul_nonneg (nodeWeights_nonneg _ _ _ _)
      (leafWeights_nonneg K t (d.children i.1) (lower _ _ Z) i.2)

theorem resetWeight_nonneg (K : ℝ) : ∀ t (d : Data Y E H m t) (Z : Space Y E H m t),
    0 ≤ resetWeight K t d Z
  | 0, d, Z => FirstHeight.sourceTerminal_nonneg d Z
  | t+1, d, Z => add_nonneg (nodeTerminal_nonneg _ _ _)
      (Finset.sum_nonneg fun i _ => mul_nonneg (nodeWeights_nonneg _ _ _ _)
        (resetWeight_nonneg K t (d.children i) (lower _ _ Z)))

theorem leafWeights_partition (K : ℝ) : ∀ t (d : Data Y E H m t) (Z : Space Y E H m t),
    resetWeight K t d Z + ∑ i, leafWeights K t d Z i = 1 := by
  intro t
  induction t with
  | zero => exact FirstHeight.sourceWeights_partition
  | succ t ih =>
    intro d Z
    change nodeTerminal (width m t) (centers K d) Z +
      (∑ i, nodeWeights (width m t) (centers K d) Z i * resetWeight K t (d.children i) (lower _ _ Z)) +
      (∑ a : Fin 8 × LeafSlot t, nodeWeights (width m t) (centers K d) Z a.1 *
        leafWeights K t (d.children a.1) (lower _ _ Z) a.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp_rw [← mul_add, ih, mul_one]
    exact nodeWeights_partition _ _ _

variable [CompleteSpace Y]
open scoped InnerProductSpace

omit [∀ t, InnerProductSpace ℝ (H t)] in
theorem leafData_valid : ∀ t (d : Data Y E H m t), Valid Y E H m t d → ∀ i : LeafSlot t,
    InverseGate.LowerBound (leafData t d i).A ∧ ‖(leafData t d i).A‖ ≤ m+1 ∧
    (∀ x z, ⟪(leafData t d i).A x,z⟫_ℝ = ⟪x,(leafData t d i).A z⟫_ℝ) ∧
    (∀ j, ‖(leafData t d i).b j‖ = InverseGate.H₀) ∧ (∀ j, ‖(leafData t d i).a j‖ = 1)
  | 0, _d, hd, i => ⟨hd.lower i, hd.opNorm i, hd.symmetric i, hd.b_norm i, hd.a_norm i⟩
  | t+1, d, hd, i => leafData_valid t (d.children i.1) (hd.1 i.1) i.2

end GradientHessian.HigherHierarchy
