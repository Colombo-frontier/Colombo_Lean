import RandomizedFO2003.LocalOverlap
import RandomizedFO2003.LocalCouplingBounds
import RandomizedFO2003.QuadraticDerivativeBounds
import RandomizedFO2003.CascadeFunction

namespace RandomizedFO2003.Cascade

open Primitives
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}

noncomputable def Data.quadraticEnergy (d : Data N E) (z : BlockProduct (N + 1) E) : ℝ :=
  ∑ i, quadratic (d.A i) (z i)

noncomputable def Data.initialForce (d : Data N E) (z : BlockProduct (N + 1) E) : ℝ := d.force 0 (z 0)

noncomputable def Data.edgeFunction (d : Data N E) (j : Fin N) : E × E → ℝ :=
  localCoupling (d.a j.castSucc) (d.b j.succ) d.B d.α d.D d.C₀ d.K

noncomputable def Data.edgeEnergy (d : Data N E) (z : BlockProduct (N + 1) E) : ℝ :=
  ∑ j, d.edgeFunction j (z j.castSucc, z j.succ)

theorem Data.quadraticEnergy_contDiff (d : Data N E) (n : ℕ) : ContDiff ℝ n d.quadraticEnergy :=
  ContDiff.sum (fun i _ => (quadratic_contDiff (d.A i) n).comp (blockProjection (E := E) (N + 1) i).contDiff)

theorem Data.initialForce_contDiff (d : Data N E) (n : ℕ) : ContDiff ℝ n d.initialForce :=
  (d.force_contDiff 0 n).comp (blockProjection (E := E) (N + 1) 0).contDiff

theorem Data.edgeFunction_contDiff (d : Data N E) (j : Fin N) (n : ℕ) : ContDiff ℝ n (d.edgeFunction j) :=
  localCoupling_contDiff _ _ _ _ _ _ _ n

theorem Data.edgeEnergy_contDiff (d : Data N E) (n : ℕ) : ContDiff ℝ n d.edgeEnergy :=
  ContDiff.sum (fun j _ => (d.edgeFunction_contDiff j n).comp (edgeProjection (E := E) N j).contDiff)

theorem Data.energy_eq_parts (d : Data N E) :
    d.energy = fun z => d.quadraticEnergy z - d.initialForce z - d.edgeEnergy z := rfl

private theorem derivative_sub_norm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) {f g : X → ℝ} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (x : X) :
    ‖iteratedFDeriv ℝ n (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n g x‖ := by
  simp only [sub_eq_add_neg]
  rw [iteratedFDeriv_add_apply' hf.contDiffAt hg.neg.contDiffAt]
  apply (norm_add_le _ _).trans_eq
  change ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n (-g) x‖ = _
  rw [iteratedFDeriv_neg_apply, norm_neg]

theorem Data.energy_derivative_norm_le_parts (d : Data N E) (n : ℕ) (x : BlockProduct (N + 1) E) :
    ‖iteratedFDeriv ℝ n d.energy x‖ ≤ ‖iteratedFDeriv ℝ n d.quadraticEnergy x‖ +
      ‖iteratedFDeriv ℝ n d.initialForce x‖ + ‖iteratedFDeriv ℝ n d.edgeEnergy x‖ := by
  rw [d.energy_eq_parts]
  apply (derivative_sub_norm_le n ((d.quadraticEnergy_contDiff n).sub (d.initialForce_contDiff n))
    (d.edgeEnergy_contDiff n) x).trans
  exact add_le_add_right (derivative_sub_norm_le n (d.quadraticEnergy_contDiff n)
    (d.initialForce_contDiff n) x) _

variable [CompleteSpace E]

theorem Data.energy_second_derivative_bound (d : Data N E)
    (hA : ∀ i, IsSelfAdjoint (d.A i)) {L M₀ Mₑ : ℝ} (hL : 0 ≤ L) (hMₑ : 0 ≤ Mₑ)
    (hAL : ∀ i, ‖d.A i‖ ≤ L) (hforce : ∀ y, ‖iteratedFDeriv ℝ 2 (d.force 0) y‖ ≤ M₀)
    (hedge : ∀ j p, ‖iteratedFDeriv ℝ 2 (d.edgeFunction j) p‖ ≤ Mₑ)
    (x : BlockProduct (N + 1) E) :
    ‖iteratedFDeriv ℝ 2 d.energy x‖ ≤ L + M₀ + 2 * Mₑ := by
  have hq : ‖iteratedFDeriv ℝ 2 d.quadraticEnergy x‖ ≤ L :=
    block_sum_second_derivative_bound (fun i => quadratic (d.A i))
      (fun i => quadratic_contDiff (d.A i) 2) hL x
      (fun i => (quadratic_second_derivative_norm (d.A i) (hA i) (x i)).trans_le (hAL i))
  have hf : ‖iteratedFDeriv ℝ 2 d.initialForce x‖ ≤ M₀ :=
    (Calculus.norm_iteratedFDeriv_comp_contraction_le (blockProjection (E := E) (N + 1) 0)
      (blockProjection_norm_le _ _) 2 (d.force_contDiff 0 2) x).trans (hforce (x 0))
  have he : ‖iteratedFDeriv ℝ 2 d.edgeEnergy x‖ ≤ 2 * Mₑ :=
    edge_sum_second_derivative_bound d.edgeFunction (fun j => d.edgeFunction_contDiff j 2)
      hMₑ x (fun j => hedge j _)
  exact (d.energy_derivative_norm_le_parts 2 x).trans (add_le_add (add_le_add hq hf) he)

theorem Data.energy_third_derivative_bound (d : Data N E)
    (hA : ∀ i, IsSelfAdjoint (d.A i)) {M₀ Mₑ : ℝ} (hMₑ : 0 ≤ Mₑ)
    (hforce : ∀ y, ‖iteratedFDeriv ℝ 3 (d.force 0) y‖ ≤ M₀)
    (hedge : ∀ j p, ‖iteratedFDeriv ℝ 3 (d.edgeFunction j) p‖ ≤ Mₑ)
    (x : BlockProduct (N + 1) E) :
    ‖iteratedFDeriv ℝ 3 d.energy x‖ ≤ M₀ + 2 * Mₑ := by
  have hq : ‖iteratedFDeriv ℝ 3 d.quadraticEnergy x‖ ≤ 0 :=
    block_sum_third_derivative_bound (fun i => quadratic (d.A i))
      (fun i => quadratic_contDiff (d.A i) 3) le_rfl x
      (fun i => by rw [quadratic_third_derivative_zero (d.A i) (hA i), norm_zero])
  have hf : ‖iteratedFDeriv ℝ 3 d.initialForce x‖ ≤ M₀ :=
    (Calculus.norm_iteratedFDeriv_comp_contraction_le (blockProjection (E := E) (N + 1) 0)
      (blockProjection_norm_le _ _) 3 (d.force_contDiff 0 3) x).trans (hforce (x 0))
  have he : ‖iteratedFDeriv ℝ 3 d.edgeEnergy x‖ ≤ 2 * Mₑ :=
    edge_sum_third_derivative_bound d.edgeFunction (fun j => d.edgeFunction_contDiff j 3)
      hMₑ x (fun j => hedge j _)
  simpa only [zero_add] using
    (d.energy_derivative_norm_le_parts 3 x).trans (add_le_add (add_le_add hq hf) he)

end RandomizedFO2003.Cascade
