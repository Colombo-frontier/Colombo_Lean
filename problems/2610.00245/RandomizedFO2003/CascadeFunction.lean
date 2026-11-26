import RandomizedFO2003.BlockGradient
import RandomizedFO2003.CascadeSpace

namespace RandomizedFO2003.Cascade

open Primitives Calculus
open scoped BigOperators

variable (N : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Data for the source's static cascade with `N + 1` blocks. Spectral and
parameter hypotheses are supplied to theorems, not hidden in the data. -/
structure Data where
  A : Fin (N + 1) → E →L[ℝ] E
  a : Fin (N + 1) → E
  b : Fin (N + 1) → E
  B : ℝ
  α : ℝ
  D : ℝ
  C₀ : ℝ
  K : ℝ

variable {N E}

noncomputable def Data.force (d : Data N E) (i : Fin (N + 1)) : E → ℝ :=
  forcing (d.b i) d.D d.C₀ d.K

noncomputable def Data.gate (d : Data N E) (i : Fin (N + 1)) : E → ℝ :=
  radialGate (d.a i) d.B d.α

/-- The exact finite sum in the construction, on the Euclidean block norm. -/
noncomputable def Data.energy (d : Data N E) (z : BlockProduct (N + 1) E) : ℝ :=
  (∑ i : Fin (N + 1), quadratic (d.A i) (z i)) - d.force 0 (z 0) -
    ∑ j : Fin N, d.gate j.castSucc (z j.castSucc) * d.force j.succ (z j.succ)

noncomputable def Data.incoming (d : Data N E) (z : BlockProduct (N + 1) E) : Fin (N + 1) → ℝ :=
  Fin.cases 1 (fun j => d.gate j.castSucc (z j.castSucc))

noncomputable def Data.outgoing (d : Data N E) (z : BlockProduct (N + 1) E) : Fin (N + 1) → ℝ :=
  Fin.lastCases 0 (fun j => d.force j.succ (z j.succ))

theorem Data.force_contDiff (d : Data N E) (i : Fin (N + 1)) (n : ℕ) : ContDiff ℝ n (d.force i) :=
  forcing_contDiff (d.b i) d.D d.C₀ d.K n

theorem Data.gate_contDiff (d : Data N E) (i : Fin (N + 1)) (n : ℕ) : ContDiff ℝ n (d.gate i) :=
  radialGate_contDiff (d.a i) d.B d.α n

theorem Data.energy_contDiff (d : Data N E) (n : ℕ) : ContDiff ℝ n d.energy := by
  have hp (i : Fin (N + 1)) : ContDiff ℝ n (fun z : BlockProduct (N + 1) E => z i) :=
    (blockProjection (E := E) (N + 1) i).contDiff
  apply ContDiff.sub
  · apply ContDiff.sub
    · apply ContDiff.sum
      intro i _hi
      exact (quadratic_contDiff (d.A i) n).comp (hp i)
    · exact (d.force_contDiff 0 n).comp (hp 0)
  · apply ContDiff.sum
    intro j _hj
    exact ((d.gate_contDiff j.castSucc n).comp (hp j.castSucc)).mul
      ((d.force_contDiff j.succ n).comp (hp j.succ))

theorem Data.gate_mem (d : Data N E) (i : Fin (N + 1)) (x : E) :
    0 ≤ d.gate i x ∧ d.gate i x ≤ 1 := ⟨gate_nonneg _, gate_le_one _⟩

@[simp] theorem Data.gate_zero (d : Data N E) (i : Fin (N + 1)) : d.gate i 0 = 0 := by
  change Primitives.gate (radialReadout (d.a i) d.B d.α 0) = 0
  have hr : radialReadout (d.a i) d.B d.α 0 = 0 := by
    simp [radialReadout, radialSquash, unitRadialSquash]
  rw [hr]
  exact gate_zero_of_le (by norm_num)

@[simp] theorem Data.force_zero (d : Data N E) (i : Fin (N + 1)) : d.force i 0 = d.D * d.C₀ :=
  forcing_zero _ _ _ _

@[simp] theorem Data.energy_zero (d : Data N E) : d.energy 0 = -(d.D * d.C₀) := by
  simp [Data.energy, quadratic]

@[simp] theorem Data.incoming_zero (d : Data N E) (z : BlockProduct (N + 1) E) : d.incoming z 0 = 1 := rfl

@[simp] theorem Data.incoming_succ (d : Data N E) (z : BlockProduct (N + 1) E) (j : Fin N) :
    d.incoming z j.succ = d.gate j.castSucc (z j.castSucc) := rfl

@[simp] theorem Data.outgoing_last (d : Data N E) (z : BlockProduct (N + 1) E) :
    d.outgoing z (Fin.last N) = 0 := by simp [Data.outgoing]

@[simp] theorem Data.outgoing_castSucc (d : Data N E) (z : BlockProduct (N + 1) E) (j : Fin N) :
    d.outgoing z j.castSucc = d.force j.succ (z j.succ) := by simp [Data.outgoing]

theorem Data.incoming_mem (d : Data N E) (z : BlockProduct (N + 1) E) (i : Fin (N + 1)) :
    0 ≤ d.incoming z i ∧ d.incoming z i ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact d.gate_mem _ _

theorem Data.force_bounds (d : Data N E) (hD : 0 ≤ d.D) (hK : 0 ≤ d.K) (hC : d.K + 2 ≤ d.C₀)
    (i : Fin (N + 1)) (x : E) :
    d.D ≤ d.force i x ∧ d.force i x ≤ d.D * (d.C₀ + d.K + 1) :=
  forcing_bounds _ hD hK hC x

theorem Data.energy_lower_bound (d : Data N E)
    (hA : ∀ i x, 0 ≤ inner (𝕜 := ℝ) x (d.A i x))
    (hD : 0 ≤ d.D) (hK : 0 ≤ d.K) (hC : d.K + 2 ≤ d.C₀) (z : BlockProduct (N + 1) E) :
    -((N + 1 : ℕ) : ℝ) * (d.D * (d.C₀ + d.K + 1)) ≤ d.energy z := by
  have hquad : 0 ≤ ∑ i : Fin (N + 1), quadratic (d.A i) (z i) := by
    apply Finset.sum_nonneg
    intro i _hi
    exact mul_nonneg (by norm_num) (hA i (z i))
  have hf := (d.force_bounds hD hK hC 0 (z 0)).2
  have he : (∑ j : Fin N, d.gate j.castSucc (z j.castSucc) * d.force j.succ (z j.succ)) ≤
      (N : ℝ) * (d.D * (d.C₀ + d.K + 1)) := by
    calc
      _ ≤ ∑ _j : Fin N, d.D * (d.C₀ + d.K + 1) := by
        apply Finset.sum_le_sum
        intro j _hj
        have hforce := d.force_bounds hD hK hC j.succ (z j.succ)
        exact (mul_le_of_le_one_left (hD.trans hforce.1) (d.gate_mem _ _).2).trans hforce.2
      _ = _ := by simp
  dsimp only [Data.energy]
  push_cast
  linarith

/-- A pairwise gap bound for the actual function, in the same form used by
`Model.InFunctionClass`; no existence of a minimizing point is needed. -/
theorem Data.initial_gap_bound (d : Data N E)
    (hA : ∀ i x, 0 ≤ inner (𝕜 := ℝ) x (d.A i x))
    (hD : 0 ≤ d.D) (hK : 0 ≤ d.K) (hC : d.K + 2 ≤ d.C₀) (z : BlockProduct (N + 1) E) :
    d.energy 0 - d.energy z ≤ ((N + 1 : ℕ) : ℝ) * (d.D * (d.C₀ + d.K + 1)) := by
  have hl := d.energy_lower_bound hA hD hK hC z
  have hC0 : 0 ≤ d.C₀ := by linarith
  rw [d.energy_zero]
  nlinarith [mul_nonneg hD hC0]

end RandomizedFO2003.Cascade
