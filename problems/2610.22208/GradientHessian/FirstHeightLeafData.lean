import GradientHessian.LeafFunctions
import GradientHessian.FirstHeightBounds
import GradientHessian.FirstHeightScales

/-! Actual leaf coefficients for one first-height node. The eight child
labels appear only in this parameter record. Their physical leaf space is
shared, with M=m+1 numerical tasks and 53 registers per task. -/

noncomputable section
namespace GradientHessian.FirstHeight
open InnerCoordinates
open scoped InnerProductSpace

def leafValueConstant : ℝ := 2 * Leaf.numericalRadius ^ 2 + Inner.innerConstant
def spacing (m : ℕ) : ℝ := leafValueConstant * (m + 1) + 56
def firstAmplitude (m : ℕ) : ℝ := amplitude 8 (spacing m) (outerRadius (m + 1))

theorem leafValueConstant_pos : 0 < leafValueConstant := by
  unfold leafValueConstant
  linarith [sq_nonneg Leaf.numericalRadius, Inner.innerConstant_pos]

theorem spacing_ge (m : ℕ) : 56 ≤ spacing m := by
  unfold spacing
  have h : 0 ≤ leafValueConstant * (m + 1) := mul_nonneg leafValueConstant_pos.le (by positivity)
  linarith

structure Data (Y E : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) where
  A : Fin 8 → Y →L[ℝ] Y
  b : Fin 8 → Fin (m + 1) → Y
  a : Fin 8 → Fin (m + 1) → Y
  innerDirections : Fin 8 → Fin (m + 1) → Fin (Inner.absoluteDepth + 2) → E
  outerDirections : Fin 8 → Fin (depth (m + 1) + 2) → E

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev SourceSpace (Y E : Type*) [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ) :=
  Space (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1))

def children (d : Data Y E m) (i : Fin 8) : Leaf.Space Y E (m + 1) → ℝ :=
  Leaf.objective (d.A i) (d.b i) (d.a i) (d.innerDirections i)
def childPorts (d : Data Y E m) (i : Fin 8) : Leaf.Space Y E (m + 1) → ℝ :=
  Leaf.outgoing (d.innerDirections i)

def sourceNode (d : Data Y E m) : SourceSpace Y E m → ℝ :=
  node (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections
def sourceResidual (d : Data Y E m) : SourceSpace Y E m → ℝ :=
  residual (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections
def sourceBaseline (m : ℕ) : SourceSpace Y E m → ℝ :=
  baseline (Leaf.publicQuadratic (m + 1)) 8 (depth (m + 1))
def sourceDriven (d : Data Y E m) (l : ℝ) : SourceSpace Y E m → ℝ :=
  driven (Leaf.publicQuadratic (m + 1)) (children d) (childPorts d) (spacing m) d.outerDirections l
def sourceOutgoing (d : Data Y E m) : SourceSpace Y E m → ℝ := Inner.outgoing d.outerDirections

theorem children_contDiff (d : Data Y E m) (i : Fin 8) : ContDiff ℝ 3 (children d i) :=
  Leaf.objective_contDiff (by omega) _ _ _ _
theorem childPorts_contDiff (d : Data Y E m) (i : Fin 8) : ContDiff ℝ 3 (childPorts d i) :=
  Inner.ports_contDiff (d.innerDirections i) (Fin.last m)
theorem childPorts_bounds (d : Data Y E m) (i : Fin 8) (Z : Leaf.Space Y E (m + 1)) :
    childPorts d i Z ∈ Set.Icc (0 : ℝ) 1 :=
  Inner.ports_bounds (d.innerDirections i) Z (Fin.last m)

theorem sourceNode_contDiff (d : Data Y E m) : ContDiff ℝ 3 (sourceNode d) :=
  node_contDiff _ _ _ _ _ (Leaf.publicQuadratic_contDiff _) (children_contDiff d) (childPorts_contDiff d)
theorem sourceDriven_contDiff (d : Data Y E m) (l : ℝ) : ContDiff ℝ 3 (sourceDriven d l) :=
  driven_contDiff _ _ _ _ _ _ (Leaf.publicQuadratic_contDiff _) (children_contDiff d) (childPorts_contDiff d)
theorem sourceResidual_contDiff (d : Data Y E m) : ContDiff ℝ 3 (sourceResidual d) :=
  residual_contDiff _ _ _ _ _ (Leaf.publicQuadratic_contDiff _) (children_contDiff d) (childPorts_contDiff d)

theorem children_relative (d : Data Y E m) (i : Fin 8) (Z : Leaf.Space Y E (m + 1)) :
    children d i Z - Leaf.publicQuadratic (m + 1) Z =
      Leaf.correction (d.A i) (d.b i) (d.a i) (d.innerDirections i) Z := by
  simp [children, Leaf.objective]

theorem sourceResidual_nonpos (d : Data Y E m) (hAn : ∀ i, ‖d.A i‖ ≤ m + 1) (Z : SourceSpace Y E m) :
    sourceResidual d Z ≤ 0 := by
  apply residual_nonpos _ _ _ (le_trans (by norm_num : (0 : ℝ) ≤ 56) (spacing_ge m))
    d.outerDirections Z
  · intro i
    rw [children_relative]
    exact Leaf.correction_nonpos _ (by simpa using hAn i) _ _ _ _
  · exact fun i => childPorts_bounds d i _

theorem sourceResidual_bounded (d : Data Y E m) (hAn : ∀ i, ‖d.A i‖ ≤ m + 1) (Z : SourceSpace Y E m)
    (hZ : ‖numerical Y E (m + 1) (Inner.absoluteDepth + 2)
      (numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z)‖ ≤ Leaf.numericalRadius) :
    -firstAmplitude m ≤ sourceResidual d Z ∧ sourceResidual d Z ≤ 0 := by
  apply residual_bounds _ _ _ (mul_nonneg leafValueConstant_pos.le (by positivity)) d.outerDirections Z
  · intro i
    rw [children_relative]
    simpa only [leafValueConstant, Nat.cast_add, Nat.cast_one, neg_mul] using
      Leaf.bounded_correction (d.A i) (by simpa using hAn i) (d.b i) (d.a i) (d.innerDirections i) _ hZ
  · exact fun i => childPorts_bounds d i _

theorem sourceNode_energy (d : Data Y E m) (hA : ∀ i, InverseGate.LowerBound (d.A i))
    (Z : SourceSpace Y E m) :
    let z := numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z
    ‖numerical Y E (m + 1) (Inner.absoluteDepth + 2) z‖ ^ 2 / 2 +
      Inner.publicQuadratic (m + 1) Inner.absoluteDepth z +
      Inner.publicQuadratic 8 (depth (m + 1)) Z - firstAmplitude m - Inner.innerConstant * (m + 1) ≤
        sourceNode d Z := by
  dsimp only
  apply global_energy _ _ _ (spacing_ge m) (mul_nonneg Inner.innerConstant_pos.le (by positivity))
    d.outerDirections Z
  · unfold Leaf.publicQuadratic
    have hm : (1 : ℝ) ≤ m + 1 := by exact_mod_cast (show 1 ≤ m + 1 by omega)
    have hn := sq_nonneg (‖numerical Y E (m + 1) (Inner.absoluteDepth + 2)
      (numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z)‖)
    have hp := mul_le_mul_of_nonneg_right hm hn
    push_cast
    nlinarith
  · intro i
    simpa only [Nat.cast_add, Nat.cast_one] using
      Leaf.objective_energy (m := m + 1) (by omega) (d.A i) (hA i)
        (d.b i) (d.a i) (d.innerDirections i)
        (numerical (Leaf.Space Y E (m + 1)) E 8 (depth (m + 1) + 2) Z)
  · exact fun i => childPorts_bounds d i _

variable [CompleteSpace Y]

/-- Only genuine source coefficient assumptions. No energy, derivative,
localization or activation conclusions are fields of this record. -/
structure Valid (d : Data Y E m) : Prop where
  lower : ∀ i, InverseGate.LowerBound (d.A i)
  opNorm : ∀ i, ‖d.A i‖ ≤ m + 1
  symmetric : ∀ i x z, ⟪d.A i x, z⟫_ℝ = ⟪x, d.A i z⟫_ℝ
  b_norm : ∀ i j, ‖d.b i j‖ = InverseGate.H₀
  a_norm : ∀ i j, ‖d.a i j‖ = 1
  certificate : ∀ i j, InverseGate.H₀ / 4 ≤
    ⟪d.a i j, InverseGate.inverse (d.A i) (lower i) (d.b i j)⟫_ℝ
  inner_unit : ∀ i j l, ‖d.innerDirections i j l‖ = 1
  outer_unit : ∀ i j, ‖d.outerDirections i j‖ = 1

end GradientHessian.FirstHeight
