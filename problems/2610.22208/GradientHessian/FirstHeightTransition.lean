import GradientHessian.FirstHeightSlices

/-! The first-height transition coefficient is nonpositive, by the ordered
payload intervals. The exclusion uses the actual last-register gradient. -/

noncomputable section
namespace GradientHessian.FirstHeight
open EuclideanRegisters InnerCoordinates

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem payload_lastSlice (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b) (x : E) :
    payload Q child childPort S v (Inner.lastSlice Z i x) = payload Q child childPort S v Z := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [payload, Inner.input, Inner.lastSlice]
  · simp [payload, Inner.lastSlice, hj]

def tailPayload (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b) : ℝ :=
  FirstHeightSelector.select b (Function.update (Inner.ports v Z) i 1)
    (payload Q child childPort S v Z) (-(b : ℝ) * S)

theorem tailPayload_le (Q : F → ℝ) (child childPort : Fin b → F → ℝ) {A₀ : ℝ} (hA : 0 ≤ A₀)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b)
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1)
    (hc : ∀ j, -A₀ ≤ child j (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ∧
      child j (numerical F E b (k + 2) Z) - Q (numerical F E b (k + 2) Z) ≤ 0)
    (ho : ∀ j, childPort j (numerical F E b (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1) :
    tailPayload Q child childPort (A₀ + 56) v Z i ≤ payload Q child childPort (A₀ + 56) v Z i :=
  FirstHeightSelector.ordered_tail b _ _ (by linarith) i (Inner.ports_bounds v Z) hprev
    (fun j => payload_interval Q child childPort v Z j (hc j) (ho j))

theorem selected_lastSlice (Q : F → ℝ) (child childPort : Fin b → F → ℝ) (S : ℝ)
    (v : Fin b → Fin (k + 2) → E) (Z : Space F E b k) (i : Fin b)
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1) (x : E) :
    selected Q child childPort S v (Inner.lastSlice Z i x) =
      (1 - Profiles.varpi (LatchChain.u (Inner.lastRadius k) (v i (Fin.last (k + 1))) x)) *
        payload Q child childPort S v Z i +
      Profiles.varpi (LatchChain.u (Inner.lastRadius k) (v i (Fin.last (k + 1))) x) *
        tailPayload Q child childPort S v Z i := by
  unfold selected
  rw [Inner.ports_lastSlice, payload_lastSlice]
  exact FirstHeightSelector.select_update_first b _ _ _ i hprev _

theorem driven_lastSlice (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ) (S : ℝ)
    (v : Fin (b + 1) → Fin (k + 2) → E) (l : ℝ) (Z : Space F E (b + 1) k) (i : Fin (b + 1))
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1) :
    ∃ a C : ℝ, ∀ x, driven Q child childPort S v l (Inner.lastSlice Z i x) =
      (LatchChain.atom a (Inner.lastRadius k) (v i (Fin.last (k + 1))) x +
        (tailPayload Q child childPort S v Z i - payload Q child childPort S v Z i -
          (if i = Fin.last b then l else 0)) *
          Profiles.varpi (LatchChain.u (Inner.lastRadius k) (v i (Fin.last (k + 1))) x)) + C := by
  obtain ⟨a, C, hC⟩ := Inner.self_last_slice (k + 1) (v i) (Inner.radius k) 0
    (tasks F E (b + 1) (k + 2) Z i)
  let C' := Q (numerical F E (b + 1) (k + 2) Z) + payload Q child childPort S v Z i + C +
    (∑ j ∈ Finset.univ.erase i, Inner.block (v j) (tasks F E (b + 1) (k + 2) Z j)) -
    if i = Fin.last b then 0 else l * Inner.outgoing v Z
  refine ⟨a, C', fun x => ?_⟩
  simp only [driven, node, selected_lastSlice Q child childPort S v Z i hprev]
  have hself : Inner.selfSum v (Inner.lastSlice Z i x) =
      LatchChain.atom a (Inner.lastRadius k) (v i (Fin.last (k + 1))) x + C +
        ∑ j ∈ Finset.univ.erase i, Inner.block (v j) (tasks F E (b + 1) (k + 2) Z j) := by
    rw [Inner.lastSlice, Inner.selfSum_task_slice]
    change LatchChain.self _ _ _ _ _ + _ = _
    rw [hC, Inner.radius_last]
  rw [hself]
  simp only [Inner.lastSlice, numerical_replaceTask]
  have hout : Inner.outgoing v (Inner.lastSlice Z i x) = if i = Fin.last b then
      Profiles.varpi (LatchChain.u (Inner.lastRadius k) (v i (Fin.last (k + 1))) x)
      else Inner.outgoing v Z := by
    unfold Inner.outgoing
    rw [Inner.ports_lastSlice]
    by_cases hi : i = Fin.last b
    · subst i; simp
    · simp [hi, Function.update_of_ne (Ne.symm hi)]
  simp only [Inner.lastSlice] at hout
  rw [hout]
  dsimp [C']
  split_ifs <;> ring

theorem lastSlice_eq_replaceRegister (Z : Space F E b k) (i : Fin b) (x : E) :
    Inner.lastSlice Z i x = replaceRegister Z i (Fin.last (k + 1)) x := by
  simp [Inner.lastSlice, replaceTask, Inner.replaceLast, replaceRegister, insertRegister]

variable [CompleteSpace F] [CompleteSpace E]

theorem lastSlice_gradient_norm_le (f : Space F E b k → ℝ) (hf : ContDiff ℝ 3 f)
    (Z : Space F E b k) (i : Fin b) :
    ‖gradient (fun x => f (Inner.lastSlice Z i x))
      (tasks F E b (k + 2) Z i (Fin.last (k + 1)))‖ ≤ ‖gradient f Z‖ := by
  simp_rw [lastSlice_eq_replaceRegister]
  exact register_slice_gradient_norm_le Z i (Fin.last (k + 1)) f
    (hf.differentiable (by norm_num) Z)

theorem first_transition_impossible (Q : F → ℝ) (child childPort : Fin (b + 1) → F → ℝ)
    {A₀ : ℝ} (hA : 0 ≤ A₀) (v : Fin (b + 1) → Fin (k + 2) → E) {l : ℝ} (hl : 0 ≤ l)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i))
    (ho : ∀ i, ContDiff ℝ 3 (childPort i)) (Z : Space F E (b + 1) k) (i : Fin (b + 1))
    (hv : ‖v i (Fin.last (k + 1))‖ = 1)
    (hprev : ∀ j, j < i → Inner.ports v Z j = 1)
    (hval : ∀ j, -A₀ ≤ child j (numerical F E (b + 1) (k + 2) Z) -
      Q (numerical F E (b + 1) (k + 2) Z) ∧
      child j (numerical F E (b + 1) (k + 2) Z) - Q (numerical F E (b + 1) (k + 2) Z) ≤ 0)
    (hop : ∀ j, childPort j (numerical F E (b + 1) (k + 2) Z) ∈ Set.Icc (0 : ℝ) 1)
    (hi0 : 0 < Inner.ports v Z i) (hi1 : Inner.ports v Z i < 1)
    (hg : ‖gradient (driven Q child childPort (A₀ + 56) v l) Z‖ ≤ 1) : False := by
  let x := tasks F E (b + 1) (k + 2) Z i (Fin.last (k + 1))
  let v' := v i (Fin.last (k + 1))
  let u := LatchChain.u (Inner.lastRadius k) v' x
  have hpi : Inner.ports v Z i = Profiles.varpi u := by
    simp [Inner.ports, Inner.completion, LatchChain.port, u, v', x]
  have hu0 : (2 / 3 : ℝ) < u := by
    by_contra h
    rw [hpi, Profiles.varpi_zero (le_of_not_gt h)] at hi0
    linarith
  have hu1 : u < (3 / 4 : ℝ) := by
    by_contra h
    rw [hpi, Profiles.varpi_one (le_of_not_gt h)] at hi1
    linarith
  let d := tailPayload Q child childPort (A₀ + 56) v Z i -
    payload Q child childPort (A₀ + 56) v Z i - (if i = Fin.last b then l else 0)
  have hd : d ≤ 0 := by
    have htail := tailPayload_le Q child childPort hA v Z i hprev hval hop
    dsimp [d]
    split_ifs <;> linarith
  have hr : 0 < Inner.lastRadius k := by unfold Inner.lastRadius; positivity
  have hcoef : d * deriv Profiles.varpi u / Inner.lastRadius k ≤ 1 / 2 := by
    have hprod := mul_nonpos_of_nonpos_of_nonneg hd (LatchProfiles.varpi_derivative_nonneg u)
    have hdiv := div_nonpos_of_nonpos_of_nonneg hprod hr.le
    linarith
  obtain ⟨a, C, hC⟩ := driven_lastSlice Q child childPort (A₀ + 56) v l Z i hprev
  have hs := (lastSlice_gradient_norm_le (driven Q child childPort (A₀ + 56) v l)
    (driven_contDiff Q child childPort (A₀ + 56) v l hQ hc ho) Z i).trans hg
  rw [funext hC] at hs
  have hh := Inner.atom_transition_hasGradientAt hr a d v' x hu0 hu1
  rw [(LatchChain.add_constant_hasGradientAt hh C).gradient] at hs
  exact (not_lt_of_ge hs) (LatchGeometry.transition_exclusion v' ((Inner.lastRadius k)⁻¹ • x)
    hv hcoef hu0 hu1)

end GradientHessian.FirstHeight
