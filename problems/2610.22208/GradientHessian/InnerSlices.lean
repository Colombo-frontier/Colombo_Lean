import GradientHessian.InnerFunctions

/-! Actual scalar and derivative restrictions of the inner objective. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def focused (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ) (i : Fin (m + 1))
    (Z : Space Y E (m + 1) (k + 2)) : ℝ :=
  InverseGate.quadratic A (numerical Y E (m + 1) (k + 2) Z) - payload b a v Z i +
    selfSum v Z - l * outgoing v Z

theorem focused_contDiff (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ) (i : Fin (m + 1)) :
    ContDiff ℝ 3 (focused A b a v l i) := by
  have hq : ContDiff ℝ 3 (InverseGate.quadratic A) :=
    contDiff_const.mul (contDiff_id.inner ℝ A.contDiff)
  exact (((hq.comp (numerical Y E (m + 1) (k + 2)).contDiff).sub
    (payload_contDiff b a v i)).add (selfSum_contDiff v)).sub
      (contDiff_const.mul (ports_contDiff v (Fin.last m)))

theorem forcingSum_fderiv_first_zero (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m)
    (hprev : ∀ j, j < i → ports v Z j = 1) (hi : ports v Z i = 0) :
    fderiv ℝ (forcingSum b a v) Z = fderiv ℝ (fun W => payload b a v W i) Z := by
  exact InnerSelector.select_fderiv_first_zero m _ _ Z
    (fun j => (ports_contDiff v j).of_le (by norm_num))
    (fun j => (payload_contDiff b a v j).of_le (by norm_num))
    (fun j W => ports_bounds v W j) i hprev hi

theorem driven_fderiv_first_zero (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1))
    (hprev : ∀ j, j < i → ports v Z j = 1) (hi : ports v Z i = 0) :
    fderiv ℝ (driven A b a v l) Z = fderiv ℝ (focused A b a v l i) Z := by
  have hq : ContDiff ℝ 3 (fun W : Space Y E (m + 1) (k + 2) =>
      InverseGate.quadratic A (numerical Y E (m + 1) (k + 2) W)) := by
    exact (contDiff_const.mul (contDiff_id.inner ℝ A.contDiff)).comp
      (numerical Y E (m + 1) (k + 2)).contDiff
  have hqd := (hq.differentiable (by norm_num) Z).hasFDerivAt
  have hF := ((forcingSum_contDiff b a v).differentiable (by norm_num) Z).hasFDerivAt
  have hP := ((payload_contDiff b a v i).differentiable (by norm_num) Z).hasFDerivAt
  have hS := ((selfSum_contDiff v).differentiable (by norm_num) Z).hasFDerivAt
  have hO := (((contDiff_const.mul (ports_contDiff v (Fin.last m))) :
    ContDiff ℝ 3 (fun W => l * outgoing v W)).differentiable (by norm_num) Z).hasFDerivAt
  have hD := (((hqd.sub hF).add hS).sub hO).fderiv
  have hJ := (((hqd.sub hP).add hS).sub hO).fderiv
  change fderiv ℝ (driven A b a v l) Z = _ at hD
  change fderiv ℝ (focused A b a v l i) Z = _ at hJ
  rw [hD, hJ, forcingSum_fderiv_first_zero b a v Z i hprev hi]

theorem focused_numerical_slice (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1)) (y : Y) :
    focused A b a v l i (replaceNumerical Z y) =
      InverseGate.objective A (b i) (a i) (input (v i) (tasks Y E (m + 1) (k + 2) Z i)) y +
      (selfSum v Z - l * outgoing v Z) := by
  simp only [focused, payload, selfSum, outgoing, ports, numerical_replaceNumerical,
    tasks_replaceNumerical, InverseGate.objective, InverseGate.g]
  ring

theorem selfSum_task_slice (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) (U : Registers E (k + 2)) :
    selfSum v (replaceTask Z i U) = block (v i) U +
      ∑ j ∈ Finset.univ.erase i, block (v j) (tasks Y E m (k + 2) Z j) := by
  unfold selfSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [tasks_replaceTask, if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem focused_task_slice (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1))
    (hc : InverseGate.gate (a i) (numerical Y E (m + 1) (k + 2) Z) = 1) :
    ∃ C : ℝ, ∀ U : Registers E (k + 2), focused A b a v l i (replaceTask Z i U) =
      (block (v i) U - input (v i) U -
        (if i = Fin.last m then l else 0) * completion (v i) U) + C := by
  let C := InverseGate.quadratic A (numerical Y E (m + 1) (k + 2) Z) -
    InverseGate.forcing (b i) (numerical Y E (m + 1) (k + 2) Z) +
    (∑ j ∈ Finset.univ.erase i, block (v j) (tasks Y E (m + 1) (k + 2) Z j)) -
    if i = Fin.last m then 0 else l * outgoing v Z
  refine ⟨C, fun U => ?_⟩
  simp only [focused, payload, numerical_replaceTask, tasks_replaceTask, if_pos rfl,
    selfSum_task_slice, hc, mul_one, outgoing, ports]
  dsimp [C]
  by_cases hi : i = Fin.last m
  · subst i
    simp only [ite_true]
    ring
  · simp only [hi, Ne.symm hi, if_false, zero_mul]
    unfold outgoing ports
    ring

variable [CompleteSpace Y] [CompleteSpace E]

theorem first_zero_opens_numerical (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ)
    (b a : Fin (m + 1) → Y) (v : Fin (m + 1) → Fin (k + 2) → E)
    (l : ℝ) (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1))
    (hb : ‖b i‖ = InverseGate.H₀) (ha : ‖a i‖ = 1)
    (hcert : InverseGate.H₀ / 4 ≤ ⟪a i, InverseGate.inverse A hA (b i)⟫_ℝ)
    (hprev : ∀ j, j < i → ports v Z j = 1) (hi : ports v Z i = 0)
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) :
    InverseGate.gate (a i) (numerical Y E (m + 1) (k + 2) Z) = 1 := by
  have he : gradient (driven A b a v l) Z = gradient (focused A b a v l i) Z := by
    simp only [gradient, driven_fderiv_first_zero A b a v l Z i hprev hi]
  rw [he] at hg
  have hs := (numerical_slice_gradient_norm_le Z (focused A b a v l i)
    ((focused_contDiff A b a v l i).differentiable (by norm_num) Z)).trans hg
  have hfun := funext (focused_numerical_slice A b a v l Z i)
  rw [hfun, (LatchChain.add_constant_hasGradientAt
    (InverseGate.objective_hasGradientAt A hsym (b i) (a i)
      (numerical Y E (m + 1) (k + 2) Z) (input (v i) (tasks Y E (m + 1) (k + 2) Z i)))
    (selfSum v Z - l * outgoing v Z)).gradient] at hs
  rw [← (InverseGate.objective_hasGradientAt A hsym (b i) (a i)
    (numerical Y E (m + 1) (k + 2) Z) (input (v i) (tasks Y E (m + 1) (k + 2) Z i))).gradient] at hs
  exact (InverseGate.numerical_activation A hA hsym (b i) (a i)
    (numerical Y E (m + 1) (k + 2) Z) hb ha hcert
    (input_bounds _ _).1 (input_bounds _ _).2 hs).1

theorem first_zero_impossible (A : Y →L[ℝ] Y) (hA : InverseGate.LowerBound A)
    (hsym : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ)
    (b a : Fin (m + 1) → Y) (v : Fin (m + 1) → Fin (k + 2) → E)
    {l : ℝ} (hl : 0 ≤ l) (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1))
    (hb : ‖b i‖ = InverseGate.H₀) (ha : ‖a i‖ = 1)
    (hcert : InverseGate.H₀ / 4 ≤ ⟪a i, InverseGate.inverse A hA (b i)⟫_ℝ)
    (hv : ∀ j, ‖v i j‖ = 1)
    (hprev : ∀ j, j < i → ports v Z j = 1) (hi : ports v Z i = 0)
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) : False := by
  have hc := first_zero_opens_numerical A hA hsym b a v l Z i hb ha hcert hprev hi hg
  have he : gradient (driven A b a v l) Z = gradient (focused A b a v l i) Z := by
    simp only [gradient, driven_fderiv_first_zero A b a v l Z i hprev hi]
  rw [he] at hg
  have hs := (task_slice_gradient_norm_le Z i (focused A b a v l i)
    ((focused_contDiff A b a v l i).differentiable (by norm_num) Z)).trans hg
  obtain ⟨C, hC⟩ := focused_task_slice A b a v l Z i hc
  rw [funext hC] at hs
  let l' := if i = Fin.last m then l else 0
  have hl' : 0 ≤ l' := by dsimp [l']; split_ifs <;> positivity
  have hdiff : DifferentiableAt ℝ (fun U : Registers E (k + 2) =>
      block (v i) U - input (v i) U - l' * completion (v i) U)
      (tasks Y E (m + 1) (k + 2) Z i) :=
    (((block_contDiff (v i)).sub (input_contDiff (v i))).sub
      (contDiff_const.mul (completion_contDiff (v i)))).differentiable (by norm_num) _
  rw [(LatchChain.add_constant_hasGradientAt hdiff.hasGradientAt C).gradient] at hs
  have hdone := (LatchChain.source_activation k (v i) (by norm_num : (1 : ℝ) ≤ 1)
    hl' hv (tasks Y E (m + 1) (k + 2) Z i) hs).2
  change ports v Z i = 1 at hdone
  linarith

end GradientHessian.Inner
