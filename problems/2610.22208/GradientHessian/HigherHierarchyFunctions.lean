import GradientHessian.HigherHierarchyData
import GradientHessian.HigherHierarchyNode

/-! Literal recursive functions on the shared Euclidean hierarchy.
Index t is source height t+1, with the exact source widths and energies. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def baseline (K : ℝ) : (t : ℕ) → Space Y E H m t → ℝ
  | 0 => FirstHeight.sourceBaseline m
  | t+1 => nodeBaseline (baseline K t) (radius m K t)

def outgoing (K : ℝ) : (t : ℕ) → Data Y E H m t → Space Y E H m t → ℝ
  | 0, d => FirstHeight.sourceOutgoing d
  | t+1, d => fun Z => nodePorts (width m t) (centers K d) Z (Fin.last 7)

def scalar (K : ℝ) : (t : ℕ) → Data Y E H m t → Space Y E H m t → ℝ
  | 0, d => FirstHeight.sourceNode d
  | t+1, d => nodeScalar (baseline K t) (fun i => scalar K t (d.children i))
      (fun i => outgoing K t (d.children i)) (spacing m K t) (radius m K t) (width m t)
      (centers K d)

def residual (K : ℝ) (t : ℕ) (d : Data Y E H m t) (Z : Space Y E H m t) : ℝ :=
  scalar K t d Z - baseline K t Z

def driven (K : ℝ) (t : ℕ) (d : Data Y E H m t) (l : ℝ) (Z : Space Y E H m t) : ℝ :=
  scalar K t d Z - l * outgoing K t d Z

theorem scalar_eq_baseline_add_residual (K : ℝ) (t : ℕ) (d : Data Y E H m t)
    (Z : Space Y E H m t) : scalar K t d Z = baseline K t Z + residual K t d Z := by
  unfold residual
  ring

theorem residual_zero_height (K : ℝ) (d : Data Y E H m 0) :
    residual K 0 d = FirstHeight.sourceResidual d := rfl

theorem outgoing_bounds (K : ℝ) (t : ℕ) (d : Data Y E H m t) (Z : Space Y E H m t) :
    outgoing K t d Z ∈ Set.Icc (0 : ℝ) 1 := by
  cases t with
  | zero => exact Inner.ports_bounds d.outerDirections Z (Fin.last 7)
  | succ t => exact nodePorts_bounds _ _ _ _

theorem baseline_contDiff {K : ℝ} (hK : 0 < K) :
    (t : ℕ) → ContDiff ℝ 3 (baseline K t : Space Y E H m t → ℝ)
  | 0 => (Leaf.publicQuadratic_contDiff _).comp
      (InnerCoordinates.numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)).contDiff
      |>.add (Inner.publicQuadratic_contDiff _ _)
  | t+1 => nodeBaseline_contDiff (F := Space Y E H m t) (E := H t) _
      (radius_pos m hK t) (baseline_contDiff hK t)

theorem outgoing_contDiff {K : ℝ} (hK : 0 < K) (t : ℕ) (d : Data Y E H m t) :
    ContDiff ℝ 3 (outgoing K t d) := by
  cases t with
  | zero => exact Inner.ports_contDiff d.outerDirections (Fin.last 7)
  | succ t =>
    exact nodePorts_contDiff (F := Space Y E H m t) (E := H t)
      (radius_pos m hK t) (width_pos m t) _ _

theorem scalar_contDiff {K : ℝ} (hK : 0 < K) :
    (t : ℕ) → (d : Data Y E H m t) → ContDiff ℝ 3 (scalar K t d)
  | 0, d => FirstHeight.sourceNode_contDiff d
  | t+1, d => nodeScalar_contDiff (F := Space Y E H m t) (E := H t)
      _ _ _ _ (radius_pos m hK t) (width_pos m t) _
      (baseline_contDiff hK t) (fun i => scalar_contDiff hK t (d.children i))
      (fun i => outgoing_contDiff hK t (d.children i))

theorem residual_contDiff {K : ℝ} (hK : 0 < K) (t : ℕ) (d : Data Y E H m t) :
    ContDiff ℝ 3 (residual K t d) :=
  (scalar_contDiff hK t d).sub (baseline_contDiff hK t)

theorem driven_contDiff {K : ℝ} (hK : 0 < K) (t : ℕ) (d : Data Y E H m t) (l : ℝ) :
    ContDiff ℝ 3 (driven K t d l) :=
  (scalar_contDiff hK t d).sub (contDiff_const.mul (outgoing_contDiff hK t d))

end GradientHessian.HigherHierarchy
