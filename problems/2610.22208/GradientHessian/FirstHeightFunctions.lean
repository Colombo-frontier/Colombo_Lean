import GradientHessian.FirstHeightSelector
import GradientHessian.InnerLemma

/-! The literal first-height scalar. All children are functions of the same
lower physical coordinate. Only the eight outer latch positions introduce
coordinates; child/node labels index coefficients, not physical spaces. -/

noncomputable section
namespace GradientHessian.FirstHeight

open EuclideanRegisters InnerCoordinates

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Space (F E : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b k : ℕ) :=
  InnerCoordinates.Space F E b (k + 2)

def payload (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b) : ℝ :=
  child i (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) -
    (i.val : ℝ) * S - Inner.input (v i) (tasks F E b (k + 2) Z i) *
      childPort i (numerical F E b (k + 2) Z)

def selected (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) : ℝ :=
  FirstHeightSelector.select b (Inner.ports v Z) (payload Q child childPort S v Z) (-(b : ℝ) * S)

def node (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) : ℝ :=
  Q (numerical F E b (k + 2) Z) + selected Q child childPort S v Z + Inner.selfSum v Z

def baseline (Q : F → ℝ) (b k : ℕ) (Z : Space F E b k) : ℝ :=
  Q (numerical F E b (k + 2) Z) + Inner.publicQuadratic b k Z

def residual (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) : ℝ :=
  node Q child childPort S v Z - baseline Q b k Z

def driven (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (Z : Space F E (b + 1) k) : ℝ :=
  node Q child childPort S v Z - l * Inner.outgoing v Z

/-- This is exactly the finite weighted expression in equation `height-one`
when `b = 8`; the zero-based index is the source's `i-1`. -/
theorem node_eq_source (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) :
    node Q child childPort S v Z = Q (numerical F E b (k + 2) Z) +
      (∑ i, InnerSelector.weight (Inner.ports v Z) i * payload Q child childPort S v Z i) -
      b * S * (∏ i, Inner.ports v Z i) + Inner.selfSum v Z := by
  simp only [node, selected, FirstHeightSelector.select_eq_inner,
    InnerSelector.select_eq_weighted_sum]
  ring

theorem residual_eq (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) :
    residual Q child childPort S v Z = selected Q child childPort S v Z + Inner.sumResidual v Z := by
  have h := Inner.residual_eq_sumResidual_sub (fun _ : Fin b => (0 : F))
    (fun _ : Fin b => (0 : F)) v Z
  unfold Inner.residual at h
  unfold residual node baseline
  linarith

theorem node_lower_slice (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (y : F) :
    node Q child childPort S v (replaceNumerical Z y) =
      (∏ i, Inner.ports v Z i) * Q y +
      (∑ i, InnerSelector.weight (Inner.ports v Z) i * child i y) -
      (∑ i, InnerSelector.weight (Inner.ports v Z) i *
        ((i.val : ℝ) * S + Inner.input (v i) (tasks F E b (k + 2) Z i) * childPort i y)) -
      b * S * (∏ i, Inner.ports v Z i) + Inner.selfSum v Z := by
  have hp : Inner.ports v (replaceNumerical Z y) = Inner.ports v Z := by
    funext i; simp [Inner.ports]
  have he : payload Q child childPort S v (replaceNumerical Z y) =
      fun i => child i y - Q y - ((i.val : ℝ) * S +
        Inner.input (v i) (tasks F E b (k + 2) Z i) * childPort i y) := by
    funext i
    simp only [payload, numerical_replaceNumerical, tasks_replaceNumerical]
    ring
  simp only [node, selected, numerical_replaceNumerical, hp, he]
  rw [FirstHeightSelector.select_sub_baseline]
  simp only [Inner.selfSum, tasks_replaceNumerical]
  ring

theorem payload_contDiff (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) (i : Fin b) :
    ContDiff ℝ 3 (fun Z => payload Q child childPort S v Z i) := by
  have hN : ContDiff ℝ 3 (numerical F E b (k + 2)) := (numerical F E b (k + 2)).contDiff
  have hI : ContDiff ℝ 3 (fun Z : Space F E b k => Inner.input (v i) (tasks F E b (k + 2) Z i)) :=
    (Inner.input_contDiff (v i)).comp (Inner.taskProjection (Y := F) (E := E) b k i).contDiff
  unfold payload
  exact ((((hc i).comp hN).sub (hQ.comp hN)).sub contDiff_const).sub
    (hI.mul ((ho i).comp hN))

theorem selected_contDiff (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) :
    ContDiff ℝ 3 (selected Q child childPort S v) :=
  FirstHeightSelector.select_contDiff b _ _ _ (Inner.ports_contDiff v)
    (payload_contDiff Q child childPort S v hQ hc ho) contDiff_const

theorem node_contDiff (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) :
    ContDiff ℝ 3 (node Q child childPort S v) :=
  ((hQ.comp (numerical F E b (k + 2)).contDiff).add
    (selected_contDiff Q child childPort S v hQ hc ho)).add (Inner.selfSum_contDiff v)

theorem residual_contDiff (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) :
    ContDiff ℝ 3 (residual Q child childPort S v) := by
  rw [funext (residual_eq Q child childPort S v)]
  exact (selected_contDiff Q child childPort S v hQ hc ho).add (Inner.sumResidual_contDiff v)

theorem driven_contDiff (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) :
    ContDiff ℝ 3 (driven Q child childPort S v l) :=
  (node_contDiff Q child childPort S v hQ hc ho).sub
    (contDiff_const.mul (Inner.ports_contDiff v (Fin.last b)))

end GradientHessian.FirstHeight
