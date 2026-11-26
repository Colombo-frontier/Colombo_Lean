import GradientHessian.FirstHeightBounds

/-! Exact restrictions of the first-height gradient at its first zero port.
All restrictions are actual affine isometric slices of the shared Euclidean
coordinate space, including at endpoints of selector plateaus. -/

noncomputable section
namespace GradientHessian.FirstHeight
open EuclideanRegisters InnerCoordinates

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def focused (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (i : Fin (b + 1))
    (Z : Space F E (b + 1) k) : ℝ :=
  Q (numerical F E (b + 1) (k + 2) Z) + payload Q child childPort S v Z i +
    Inner.selfSum v Z - l * Inner.outgoing v Z

theorem focused_contDiff (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (i : Fin (b + 1))
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i))
    (ho : ∀ i, ContDiff ℝ 3 (childPort i)) : ContDiff ℝ 3 (focused Q child childPort S v l i) :=
  (((hQ.comp (numerical F E (b + 1) (k + 2)).contDiff).add
    (payload_contDiff Q child childPort S v hQ hc ho i)).add (Inner.selfSum_contDiff v)).sub
      (contDiff_const.mul (Inner.ports_contDiff v (Fin.last b)))

theorem selected_fderiv_first_zero (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Space F E b k) (i : Fin b)
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1) (hi : Inner.ports v Z i = 0) :
    fderiv ℝ (selected Q child childPort S v) Z =
      fderiv ℝ (fun W => payload Q child childPort S v W i) Z :=
  FirstHeightSelector.select_fderiv_first_zero b _ _ _ Z
    (fun j => (Inner.ports_contDiff v j).of_le (by norm_num))
    (fun j => (payload_contDiff Q child childPort S v hQ hc ho j).of_le (by norm_num))
    contDiff_const (fun j W => Inner.ports_bounds v W j) i hprev hi

theorem driven_fderiv_first_zero (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Space F E (b + 1) k) (i : Fin (b + 1))
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1) (hi : Inner.ports v Z i = 0) :
    fderiv ℝ (driven Q child childPort S v l) Z =
      fderiv ℝ (focused Q child childPort S v l i) Z := by
  have hqd := ((hQ.comp (numerical F E (b + 1) (k + 2)).contDiff).differentiable
    (by norm_num) Z).hasFDerivAt
  have hsel := ((selected_contDiff Q child childPort S v hQ hc ho).differentiable
    (by norm_num) Z).hasFDerivAt
  have hp := ((payload_contDiff Q child childPort S v hQ hc ho i).differentiable
    (by norm_num) Z).hasFDerivAt
  have hs := ((Inner.selfSum_contDiff v).differentiable (by norm_num) Z).hasFDerivAt
  have hout := (((contDiff_const.mul (Inner.ports_contDiff v (Fin.last b))) :
    ContDiff ℝ 3 (fun W => l * Inner.outgoing v W)).differentiable (by norm_num) Z).hasFDerivAt
  have hd := (((hqd.add hsel).add hs).sub hout).fderiv
  have hf := (((hqd.add hp).add hs).sub hout).fderiv
  change fderiv ℝ (driven Q child childPort S v l) Z = _ at hd
  change fderiv ℝ (focused Q child childPort S v l i) Z = _ at hf
  rw [hd, hf, selected_fderiv_first_zero Q child childPort S v hQ hc ho Z i hprev hi]

theorem focused_lower_slice (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space F E (b + 1) k) (i : Fin (b + 1)) (y : F) :
    focused Q child childPort S v l i (replaceNumerical Z y) =
      (child i y - Inner.input (v i) (tasks F E (b + 1) (k + 2) Z i) * childPort i y) +
        (-(i.val : ℝ) * S + Inner.selfSum v Z - l * Inner.outgoing v Z) := by
  simp only [focused, payload, numerical_replaceNumerical, tasks_replaceNumerical,
    Inner.selfSum, Inner.outgoing, Inner.ports]
  ring

theorem focused_task_slice (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space F E (b + 1) k) (i : Fin (b + 1))
    (hop : childPort i (numerical F E (b + 1) (k + 2) Z) = 1) :
    ∃ C : ℝ, ∀ U : Registers E (k + 2),
      focused Q child childPort S v l i (replaceTask Z i U) =
        (Inner.block (v i) U - Inner.input (v i) U -
          (if i = Fin.last b then l else 0) * Inner.completion (v i) U) + C := by
  let C := child i (numerical F E (b + 1) (k + 2) Z) - (i.val : ℝ) * S +
    (∑ j ∈ Finset.univ.erase i, Inner.block (v j) (tasks F E (b + 1) (k + 2) Z j)) -
    if i = Fin.last b then 0 else l * Inner.outgoing v Z
  refine ⟨C, fun U => ?_⟩
  simp only [focused, payload, numerical_replaceTask, tasks_replaceTask, if_pos rfl,
    Inner.selfSum_task_slice, hop, mul_one, Inner.outgoing, Inner.ports]
  dsimp [C]
  by_cases hi : i = Fin.last b
  · subst i; simp only [ite_true]; ring
  · simp only [hi, Ne.symm hi, if_false, zero_mul]
    unfold Inner.outgoing Inner.ports
    ring

variable [CompleteSpace F] [CompleteSpace E]

/-- The actual shared lower-coordinate slice of a small full gradient is
the selected child with its nonnegative incoming outgoing coefficient. -/
theorem first_zero_child_gradient (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Space F E (b + 1) k) (i : Fin (b + 1))
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1) (hi : Inner.ports v Z i = 0)
    (hg : ‖gradient (driven Q child childPort S v l) Z‖ ≤ 1) :
    ‖gradient (fun y => child i y - Inner.input (v i) (tasks F E (b + 1) (k + 2) Z i) *
      childPort i y) (numerical F E (b + 1) (k + 2) Z)‖ ≤ 1 := by
  have he : gradient (driven Q child childPort S v l) Z =
      gradient (focused Q child childPort S v l i) Z := by
    simp only [gradient, driven_fderiv_first_zero Q child childPort S v l hQ hc ho Z i hprev hi]
  rw [he] at hg
  have hs := (numerical_slice_gradient_norm_le Z (focused Q child childPort S v l i)
    ((focused_contDiff Q child childPort S v l i hQ hc ho).differentiable (by norm_num) Z)).trans hg
  have hdiff : DifferentiableAt ℝ (fun y => child i y -
      Inner.input (v i) (tasks F E (b + 1) (k + 2) Z i) * childPort i y)
      (numerical F E (b + 1) (k + 2) Z) :=
    ((hc i).sub (contDiff_const.mul (ho i))).differentiable (by norm_num) _
  rw [funext (focused_lower_slice Q child childPort S v l Z i),
    (LatchChain.add_constant_hasGradientAt hdiff.hasGradientAt _).gradient] at hs
  exact hs

/-- Once the actual child activation theorem opens the child port, the
source incoming-one latch theorem excludes a zero outer port. -/
theorem first_zero_impossible (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) {l : ℝ} (hl : 0 ≤ l) (hQ : ContDiff ℝ 3 Q)
    (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Space F E (b + 1) k) (i : Fin (b + 1)) (hv : ∀ j, ‖v i j‖ = 1)
    (hchild : ∀ d, 0 ≤ d → ∀ y, ‖gradient (fun x => child i x - d * childPort i x) y‖ ≤ 1 →
      childPort i y = 1)
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1) (hi : Inner.ports v Z i = 0)
    (hg : ‖gradient (driven Q child childPort S v l) Z‖ ≤ 1) : False := by
  have hchildgrad := first_zero_child_gradient Q child childPort S v l hQ hc ho Z i hprev hi hg
  have hop := hchild _ (Inner.input_bounds _ _).1 _ hchildgrad
  have he : gradient (driven Q child childPort S v l) Z =
      gradient (focused Q child childPort S v l i) Z := by
    simp only [gradient, driven_fderiv_first_zero Q child childPort S v l hQ hc ho Z i hprev hi]
  rw [he] at hg
  have hs := (task_slice_gradient_norm_le Z i (focused Q child childPort S v l i)
    ((focused_contDiff Q child childPort S v l i hQ hc ho).differentiable (by norm_num) Z)).trans hg
  obtain ⟨C, hC⟩ := focused_task_slice Q child childPort S v l Z i hop
  rw [funext hC] at hs
  let l' := if i = Fin.last b then l else 0
  have hl' : 0 ≤ l' := by dsimp [l']; split_ifs <;> positivity
  have hdiff : DifferentiableAt ℝ (fun U : Registers E (k + 2) =>
      Inner.block (v i) U - Inner.input (v i) U - l' * Inner.completion (v i) U)
      (tasks F E (b + 1) (k + 2) Z i) :=
    (((Inner.block_contDiff (v i)).sub (Inner.input_contDiff (v i))).sub
      (contDiff_const.mul (Inner.completion_contDiff (v i)))).differentiable (by norm_num) _
  rw [(LatchChain.add_constant_hasGradientAt hdiff.hasGradientAt C).gradient] at hs
  have hdone := (LatchChain.source_activation k (v i) (by norm_num : (1 : ℝ) ≤ 1)
    hl' hv (tasks F E (b + 1) (k + 2) Z i) hs).2
  change Inner.ports v Z i = 1 at hdone
  linarith

end GradientHessian.FirstHeight
