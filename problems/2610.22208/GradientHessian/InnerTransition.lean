import GradientHessian.InnerSlices
import GradientHessian.InnerLastRegister

/-! Exact last-register restriction of the first unfinished task and
exclusion of every nontrivial selector transition. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lastSlice (Z : Space Y E m (k + 2)) (i : Fin m) (x : E) : Space Y E m (k + 2) :=
  replaceTask Z i (replaceLast (k + 1) (tasks Y E m (k + 2) Z i) x)

theorem lastSlice_contDiff (Z : Space Y E m (k + 2)) (i : Fin m) :
    ContDiff ℝ 3 (lastSlice Z i) := by
  unfold lastSlice replaceTask replaceLast
  exact contDiff_const.add ((insertTask Y E m (k + 2) i).contDiff.comp
    ((contDiff_const.add ((single E (k + 2) (Fin.last (k + 1))).contDiff.comp
      (contDiff_id.sub contDiff_const))).sub contDiff_const))

@[simp] theorem completion_replaceLast (v : Fin (k + 2) → E) (U : Registers E (k + 2)) (x : E) :
    completion v (replaceLast (k + 1) U x) =
      Profiles.varpi (LatchChain.u (lastRadius k) (v (Fin.last (k + 1))) x) := by
  simp [completion, LatchChain.port]

theorem ports_lastSlice (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2))
    (i : Fin m) (x : E) : ports v (lastSlice Z i x) = Function.update (ports v Z) i
      (Profiles.varpi (LatchChain.u (lastRadius k) (v i (Fin.last (k + 1))) x)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [ports, lastSlice]
  · simp [ports, lastSlice, hj, Function.update_of_ne hj]

theorem payload_lastSlice (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) (x : E) :
    payload b a v (lastSlice Z i x) = payload b a v Z := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [payload, input, lastSlice]
  · simp [payload, lastSlice, hj]

def tailPayload (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) : ℝ :=
  InnerSelector.select m (Function.update (ports v Z) i 1) (payload b a v Z)

theorem tailPayload_bounds (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) : tailPayload b a v Z i ∈ Set.Icc (0 : ℝ) payloadBound := by
  apply InnerSelector.select_bounds m _ _ payloadBound_pos.le _ (payload_bounds b a v Z)
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hj] using ports_bounds v Z j

theorem forcingSum_lastSlice (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) (i : Fin m) (hprev : ∀ j, j < i → ports v Z j = 1) (x : E) :
    forcingSum b a v (lastSlice Z i x) =
      (1 - Profiles.varpi (LatchChain.u (lastRadius k) (v i (Fin.last (k + 1))) x)) * payload b a v Z i +
      Profiles.varpi (LatchChain.u (lastRadius k) (v i (Fin.last (k + 1))) x) * tailPayload b a v Z i := by
  unfold forcingSum
  rw [ports_lastSlice, payload_lastSlice]
  exact InnerSelector.select_update_first m _ _ i hprev _

theorem driven_lastSlice (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1))
    (hprev : ∀ j, j < i → ports v Z j = 1) :
    ∃ a' C : ℝ, ∀ x, driven A b a v l (lastSlice Z i x) =
      (LatchChain.atom a' (lastRadius k) (v i (Fin.last (k + 1))) x +
        (payload b a v Z i - tailPayload b a v Z i - (if i = Fin.last m then l else 0)) *
          Profiles.varpi (LatchChain.u (lastRadius k) (v i (Fin.last (k + 1))) x)) + C := by
  obtain ⟨a', C, hC⟩ := self_last_slice (k + 1) (v i) (radius k) 0
    (tasks Y E (m + 1) (k + 2) Z i)
  let C' := InverseGate.quadratic A (numerical Y E (m + 1) (k + 2) Z) - payload b a v Z i + C +
    (∑ j ∈ Finset.univ.erase i, block (v j) (tasks Y E (m + 1) (k + 2) Z j)) -
    if i = Fin.last m then 0 else l * outgoing v Z
  refine ⟨a', C', fun x => ?_⟩
  simp only [driven, objective, forcingSum_lastSlice b a v Z i hprev]
  have hself : selfSum v (lastSlice Z i x) =
      LatchChain.atom a' (lastRadius k) (v i (Fin.last (k + 1))) x + C +
        ∑ j ∈ Finset.univ.erase i, block (v j) (tasks Y E (m + 1) (k + 2) Z j) := by
    rw [lastSlice, selfSum_task_slice]
    change LatchChain.self _ _ _ _ _ + _ = _
    rw [hC, radius_last]
  rw [hself]
  simp only [lastSlice, numerical_replaceTask]
  have hout : outgoing v (lastSlice Z i x) = if i = Fin.last m then
      Profiles.varpi (LatchChain.u (lastRadius k) (v i (Fin.last (k + 1))) x) else outgoing v Z := by
    unfold outgoing
    rw [ports_lastSlice]
    by_cases hi : i = Fin.last m
    · subst i
      simp
    · simp [hi, Function.update_of_ne (Ne.symm hi)]
  simp only [lastSlice] at hout
  rw [hout]
  dsimp [C']
  split_ifs <;> ring

variable [CompleteSpace Y] [CompleteSpace E]

theorem lastSlice_gradient_norm_le (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) (l : ℝ)
    (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1)) :
    ‖gradient (fun x => driven A b a v l (lastSlice Z i x))
      (tasks Y E (m + 1) (k + 2) Z i (Fin.last (k + 1)))‖ ≤ ‖gradient (driven A b a v l) Z‖ := by
  have ht := task_slice_gradient_norm_le Z i (driven A b a v l)
    ((driven_contDiff A b a v l).differentiable (by norm_num) Z)
  have hcd : ContDiff ℝ 3 (fun U => driven A b a v l (replaceTask Z i U)) := by
    exact (driven_contDiff A b a v l).comp
      (contDiff_const.add ((insertTask Y E (m + 1) (k + 2) i).contDiff.comp
        (contDiff_id.sub contDiff_const)))
  have hs := affine_centered_gradient_norm_le (single E (k + 2) (Fin.last (k + 1)))
    (single_norm_le E (k + 2) (Fin.last (k + 1))) (tasks Y E (m + 1) (k + 2) Z i)
    (tasks Y E (m + 1) (k + 2) Z i (Fin.last (k + 1)))
    (fun U => driven A b a v l (replaceTask Z i U))
    (hcd.differentiable (by norm_num) _)
  exact hs.trans ht

theorem first_transition_impossible (A : Y →L[ℝ] Y) (b a : Fin (m + 1) → Y)
    (v : Fin (m + 1) → Fin (k + 2) → E) {l : ℝ} (hl : 0 ≤ l)
    (hR : 144 * payloadBound ≤ lastRadius k)
    (Z : Space Y E (m + 1) (k + 2)) (i : Fin (m + 1))
    (hv : ‖v i (Fin.last (k + 1))‖ = 1)
    (hprev : ∀ j, j < i → ports v Z j = 1)
    (hi0 : 0 < ports v Z i) (hi1 : ports v Z i < 1)
    (hg : ‖gradient (driven A b a v l) Z‖ ≤ 1) : False := by
  let x := tasks Y E (m + 1) (k + 2) Z i (Fin.last (k + 1))
  let v' := v i (Fin.last (k + 1))
  let u := LatchChain.u (lastRadius k) v' x
  have hpi : ports v Z i = Profiles.varpi u := by simp [ports, completion, LatchChain.port, u, v', x]
  have hu0 : (2 / 3 : ℝ) < u := by
    by_contra h
    rw [hpi, Profiles.varpi_zero (le_of_not_gt h)] at hi0
    linarith [payloadBound_pos]
  have hu1 : u < (3 / 4 : ℝ) := by
    by_contra h
    rw [hpi, Profiles.varpi_one (le_of_not_gt h)] at hi1
    linarith
  let d := payload b a v Z i - tailPayload b a v Z i - (if i = Fin.last m then l else 0)
  have hd : d ≤ payloadBound := by
    have hp := (payload_bounds b a v Z i).2
    have ht := (tailPayload_bounds b a v Z i).1
    dsimp [d]
    split_ifs <;> linarith
  have hder0 := LatchProfiles.varpi_derivative_nonneg u
  have hder := varpi_derivative_bound u
  have hr : 0 < lastRadius k := by unfold lastRadius; positivity
  have hcoef : d * deriv Profiles.varpi u / lastRadius k ≤ 1 / 2 := by
    rw [div_le_iff₀ hr]
    have hm := mul_le_mul_of_nonneg_right hd hder0
    have hn := mul_le_mul_of_nonneg_left hder payloadBound_pos.le
    calc
      d * deriv Profiles.varpi u ≤ payloadBound * 36 := hm.trans hn
      _ ≤ (1 / 2 : ℝ) * (144 * payloadBound) := by
        nlinarith only [payloadBound_pos]
      _ ≤ (1 / 2 : ℝ) * lastRadius k :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
  obtain ⟨a', C, hC⟩ := driven_lastSlice A b a v l Z i hprev
  have hs := (lastSlice_gradient_norm_le A b a v l Z i).trans hg
  rw [funext hC] at hs
  have hh := atom_transition_hasGradientAt hr a' d v' x hu0 hu1
  rw [(LatchChain.add_constant_hasGradientAt hh C).gradient] at hs
  have hbad := LatchGeometry.transition_exclusion v' ((lastRadius k)⁻¹ • x) hv hcoef hu0 hu1
  exact (not_lt_of_ge hs) hbad

end GradientHessian.Inner
