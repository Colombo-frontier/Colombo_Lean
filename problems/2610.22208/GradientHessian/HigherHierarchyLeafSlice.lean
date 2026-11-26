import GradientHessian.HigherHierarchyValues

/-! The actual shared leaf coordinate and its isometric affine slices.
All higher node data label coefficients, never additional leaf coordinates. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open InnerCoordinates

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def leafProjection : (t : ℕ) → Space Y E H m t →L[ℝ] Leaf.Space Y E (m+1)
  | 0 => numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)
  | t+1 => (leafProjection t).comp (lower (Space Y E H m t) (H t))

def leafInjection : (t : ℕ) → Leaf.Space Y E (m+1) →L[ℝ] Space Y E H m t
  | 0 => insertNumerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)
  | t+1 => (insertLower (Space Y E H m t) (H t)).comp (leafInjection t)

@[simp] theorem leafProjection_leafInjection : (t : ℕ) → ∀ z : Leaf.Space Y E (m+1),
    leafProjection t (leafInjection (H := H) t z) = z
  | 0, z => rfl
  | t+1, z => by
    change leafProjection t (lower (Space Y E H m t) (H t)
      (insertLower (Space Y E H m t) (H t) (leafInjection t z))) = z
    rw [lower_insertLower, leafProjection_leafInjection t]

theorem leafInjection_norm : (t : ℕ) → ∀ z : Leaf.Space Y E (m+1),
    ‖leafInjection (H := H) t z‖ = ‖z‖
  | 0, z => insertNumerical_norm _ _ _ _ z
  | t+1, z => by
    change ‖insertLower (Space Y E H m t) (H t) (leafInjection t z)‖ = ‖z‖
    rw [insertLower_norm, leafInjection_norm t]

theorem leafInjection_norm_le (t : ℕ) : ‖leafInjection (Y := Y) (E := E) (H := H) (m := m) t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [leafInjection_norm, one_mul, le_refl]

def replaceLeaf (t : ℕ) (Z : Space Y E H m t) (z : Leaf.Space Y E (m+1)) : Space Y E H m t :=
  Z + leafInjection t (z-leafProjection t Z)

@[simp] theorem replaceLeaf_self (t : ℕ) (Z : Space Y E H m t) :
    replaceLeaf t Z (leafProjection t Z) = Z := by simp [replaceLeaf]

@[simp] theorem leafProjection_replaceLeaf (t : ℕ) (Z : Space Y E H m t) (z : Leaf.Space Y E (m+1)) :
    leafProjection t (replaceLeaf t Z z) = z := by simp [replaceLeaf]

theorem replaceLeaf_zero (Z : Space Y E H m 0) (z : Leaf.Space Y E (m+1)) :
    replaceLeaf 0 Z z = replaceNumerical Z z := rfl

theorem replaceLeaf_succ (t : ℕ) (Z : Space Y E H m (t+1)) (z : Leaf.Space Y E (m+1)) :
    replaceLeaf (t+1) Z z = replaceLower Z (replaceLeaf t (lower _ _ Z) z) := by
  change Z + (show Space Y E H m (t+1) from insertLower (Space Y E H m t) (H t)
      (leafInjection t (z-leafProjection t (lower _ _ Z)))) = _
  simp only [replaceLower, replaceLeaf, add_sub_cancel_left]

theorem numericalProjection_eq (t : ℕ) (Z : Space Y E H m t) :
    numericalProjection t Z = numerical Y E (m+1) (Inner.absoluteDepth+2) (leafProjection t Z) := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih (Z := lower _ _ Z)

theorem replaceLeaf_contDiff (t : ℕ) (Z : Space Y E H m t) : ContDiff ℝ 3 (replaceLeaf t Z) := by
  have hi := (leafInjection (Y := Y) (E := E) (H := H) (m := m) t).contDiff (n := 3)
  exact contDiff_const.add (hi.comp (contDiff_id.sub contDiff_const))

theorem outgoing_replaceLeaf (K : ℝ) (t : ℕ) (d : Data Y E H m t)
    (Z : Space Y E H m t) (z : Leaf.Space Y E (m+1)) :
    outgoing K t d (replaceLeaf t Z z) = outgoing K t d Z := by
  cases t with
  | zero => simp [outgoing, FirstHeight.sourceOutgoing, Inner.outgoing, Inner.ports, replaceLeaf_zero]
  | succ t => simp [outgoing, nodePorts, replaceLeaf_succ]

theorem baseline_replaceLeaf (K : ℝ) (t : ℕ) (Z : Space Y E H m t) (z : Leaf.Space Y E (m+1)) :
    baseline K t (replaceLeaf t Z z) =
      Leaf.publicQuadratic (Y := Y) (E := E) (m+1) z +
        (baseline K t Z-Leaf.publicQuadratic (Y := Y) (E := E) (m+1) (leafProjection t Z)) := by
  induction t with
  | zero =>
    simp only [baseline, FirstHeight.sourceBaseline, FirstHeight.baseline, replaceLeaf_zero,
      numerical_replaceNumerical, leafProjection, Inner.publicQuadratic, LatchChain.publicQuadratic,
      tasks_replaceNumerical]
    have algebra (a b c : ℝ) : a+b = a+(c+b-c) := by ring
    exact algebra _ _ _
  | succ t ih =>
    simp only [baseline, nodeBaseline, replaceLeaf_succ, lower_replaceLower, parent_replaceLower,
      leafProjection, ContinuousLinearMap.comp_apply]
    rw [ih]
    have algebra (a b c d : ℝ) : a+(b-c)+d = a+(b+d-c) := by ring
    exact algebra _ _ _ _

variable [CompleteSpace Y] [CompleteSpace E] [∀ t, CompleteSpace (H t)]

theorem leaf_gradient_norm_le (t : ℕ) (f : Space Y E H m t → ℝ) (Z : Space Y E H m t)
    (hf : DifferentiableAt ℝ f Z) :
    ‖gradient (fun z => f (replaceLeaf t Z z)) (leafProjection t Z)‖ ≤ ‖gradient f Z‖ := by
  exact affine_centered_gradient_norm_le
    (leafInjection (Y := Y) (E := E) (H := H) (m := m) t)
    (leafInjection_norm_le t) Z (leafProjection t Z) f hf

end GradientHessian.HigherHierarchy
