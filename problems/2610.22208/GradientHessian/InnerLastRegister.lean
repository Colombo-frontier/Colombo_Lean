import GradientHessian.InnerFunctions

/-! The last physical register of a latch, including its exact transition
gradient. The outgoing coefficient is allowed to be arbitrarily favorable. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates Filter
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def replaceLast (n : ℕ) (U : Registers E (n + 1)) (x : E) : Registers E (n + 1) :=
  U + single E (n + 1) (Fin.last n) (x - U (Fin.last n))

@[simp] theorem replaceLast_apply (n : ℕ) (U : Registers E (n + 1)) (x : E) (j : Fin (n + 1)) :
    replaceLast n U x j = if j = Fin.last n then x else U j := by
  by_cases h : j = Fin.last n
  · subst j
    simp [replaceLast, PiLp.add_apply]
  · simp [replaceLast, PiLp.add_apply, h]
@[simp] theorem replaceLast_self (n : ℕ) (U : Registers E (n + 1)) :
    replaceLast n U (U (Fin.last n)) = U := by simp [replaceLast]
@[simp] theorem replaceLast_last (n : ℕ) (U : Registers E (n + 1)) (x : E) :
    replaceLast n U x (Fin.last n) = x := by simp
@[simp] theorem replaceLast_head (n : ℕ) (U : Registers E (n + 2)) (x : E) :
    replaceLast (n + 1) U x 0 = U 0 := by
  rw [replaceLast_apply, if_neg]
  intro h
  have hh := congrArg Fin.val h
  simp at hh
@[simp] theorem tail_replaceLast (n : ℕ) (U : Registers E (n + 2)) (x : E) :
    tail E (n + 1) (replaceLast (n + 1) U x) = replaceLast n (tail E (n + 1) U) x := by
  ext j
  simp only [tail_apply, replaceLast_apply]
  have hj : j.succ = Fin.last (n + 1) ↔ j = Fin.last n := by
    change j.succ = (Fin.last n).succ ↔ j = Fin.last n
    exact Fin.succ_inj
  simp only [hj]

theorem self_last_slice (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (a : ℝ) (U : Registers E (n + 1)) :
    ∃ a' C : ℝ, ∀ x, LatchChain.self n v r a (replaceLast n U x) =
      LatchChain.atom a' (r (Fin.last n)) (v (Fin.last n)) x + C := by
  induction n generalizing a with
  | zero =>
    refine ⟨a, 0, fun x => ?_⟩
    simp [LatchChain.self]
  | succ n ih =>
    obtain ⟨a', C, hC⟩ := ih (fun i => v i.succ) (fun i => r i.succ)
      (Profiles.chi (LatchChain.u (r 0) (v 0) (U 0))) (tail E (n + 1) U)
    refine ⟨a', C + LatchChain.atom a (r 0) (v 0) (U 0), fun x => ?_⟩
    rw [LatchChain.self, replaceLast_head, tail_replaceLast, hC]
    change LatchChain.atom a (r 0) (v 0) (U 0) +
      (LatchChain.atom a' (r (Fin.last (n + 1))) (v (Fin.last (n + 1))) x + C) = _
    ring

theorem varpi_derivative_bound (u : ℝ) : deriv Profiles.varpi u ≤ 36 := by
  rw [(LatchProfiles.varpi_derivative u).deriv]
  have h := (Profiles.derivative_bounds (12 * (u - 2 / 3))).2
  rw [(Profiles.step_derivative _).deriv] at h
  linarith

variable [CompleteSpace E]

theorem atom_transition_hasGradientAt {r : ℝ} (hr : 0 < r) (a d : ℝ) (v x : E)
    (hu0 : 2 / 3 < LatchChain.u r v x) (hu1 : LatchChain.u r v x < 3 / 4) :
    HasGradientAt (fun y => LatchChain.atom a r v y + d * Profiles.varpi (LatchChain.u r v y))
      ((8 : ℝ) • (r⁻¹ • x) -
        (8 - d * deriv Profiles.varpi (LatchChain.u r v x) / r) •
          fderiv ℝ (RadialSquash.squash 8) (r⁻¹ • x) v) x := by
  have hxhalf : (1 / 2 : ℝ) < LatchChain.u r v x := by linarith
  have hn : ∀ᶠ y in 𝓝 x, (1 / 2 : ℝ) < LatchChain.u r v y :=
    (LatchChain.u_contDiff r v).continuous.continuousAt.eventually (Ioi_mem_nhds hxhalf)
  have he : (fun y => LatchChain.atom a r v y + d * Profiles.varpi (LatchChain.u r v y)) =ᶠ[𝓝 x]
      (fun y => r * LatchActivation.potential v 0 (-d / r) (r⁻¹ • y)) := by
    filter_upwards [hn] with y hy
    simp only [LatchChain.atom, Profiles.chi_one hy.le, sub_self, zero_mul, add_zero]
    unfold LatchActivation.potential LatchChain.u
    field_simp
    ring
  have h := (LatchChain.scaled_potential_hasGradientAt hr.ne' v x 0 (-d / r)).congr_of_eventuallyEq he
  have he' : deriv IntegralProfiles.ell₀ (LatchChain.u r v x) = 1 :=
    LatchProfiles.ell₀_derivative_identity (by rw [abs_le]; constructor <;> linarith)
  convert h using 1
  unfold LatchActivation.force
  change _ = 8 • (r⁻¹ • x) -
    (8 * deriv IntegralProfiles.ell₀ (LatchChain.u r v x) + 0 * deriv Profiles.chi _ +
      (-d / r) * deriv Profiles.varpi (LatchChain.u r v x)) • _
  rw [he']
  congr 2
  ring

theorem last_register_transition_excluded {r : ℝ} (hr : 0 < r) (a d : ℝ) (v x : E)
    (hv : ‖v‖ = 1) (hu0 : 2 / 3 < LatchChain.u r v x)
    (hu1 : LatchChain.u r v x < 3 / 4)
    (hcoef : d * deriv Profiles.varpi (LatchChain.u r v x) / r ≤ 1 / 2) :
    1 < ‖gradient (fun y => LatchChain.atom a r v y + d * Profiles.varpi (LatchChain.u r v y)) x‖ := by
  rw [(atom_transition_hasGradientAt hr a d v x hu0 hu1).gradient]
  exact LatchGeometry.transition_exclusion v (r⁻¹ • x) hv hcoef hu0 hu1

end GradientHessian.Inner
