import RandomizedFO2003.CascadeCensoring

namespace RandomizedFO2003.Cascade

open Primitives Calculus
open scoped BigOperators

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Remove just the quadratic term whose matrix is hidden from the decoder. -/
noncomputable def Data.eraseOperator (d : Data N E) (i : Fin (N + 1)) : Data N E :=
  { d with A := Function.update d.A i 0 }

theorem Data.eraseOperator_energy (d : Data N E) (i : Fin (N + 1))
    (z : BlockProduct (N + 1) E) :
    (d.eraseOperator i).energy z + quadratic (d.A i) (z i) = d.energy z := by
  classical
  have hq (j : Fin (N + 1)) : quadratic (d.A j) (z j) =
      quadratic ((d.eraseOperator i).A j) (z j) + if j = i then quadratic (d.A i) (z i) else 0 := by
    by_cases hji : j = i
    · subst j
      simp [eraseOperator, quadratic]
    · simp [eraseOperator, Function.update_of_ne hji, hji]
  have hs := congrArg (fun f : Fin (N + 1) → ℝ => ∑ j, f j) (funext hq)
  simp only [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  dsimp only [Data.energy]
  change _ + _ = (∑ j, quadratic (d.A j) (z j)) - d.force 0 (z 0) - _
  rw [hs]
  simp only [show (d.eraseOperator i).force = d.force from rfl,
    show (d.eraseOperator i).gate = d.gate from rfl]
  ring

variable [CompleteSpace E]

/-- One physical matrix response restores the exact gradient contribution. -/
theorem Data.eraseOperator_gradient (d : Data N E) (i : Fin (N + 1))
    (hA : IsSelfAdjoint (d.A i)) (z : BlockProduct (N + 1) E) :
    gradient (d.eraseOperator i).energy z + blockEmbed i (d.A i (z i)) = gradient d.energy z := by
  have hg := hasGradientAt_add
    (((d.eraseOperator i).energy_contDiff 1).differentiable (by norm_num) z).hasGradientAt
    (hasGradientAt_block i z (quadratic_hasGradientAt (d.A i) hA (z i)))
  have he : (fun x => (d.eraseOperator i).energy x + quadratic (d.A i) (x i)) = d.energy :=
    funext (d.eraseOperator_energy i)
  rw [he] at hg
  exact hg.gradient.symm

/-- The decoder receives the query, an available force vector, and a single
physical matrix response. It does not inspect the removed coefficients. -/
noncomputable def Data.reconstruct (d : Data N E) (i : Fin (N + 1))
    (b v : E) (z : BlockProduct (N + 1) E) : ℝ × BlockProduct (N + 1) E :=
  let proxy := ((d.censorGate i).replaceForce i b).eraseOperator i
  (proxy.energy z + (1 / 2 : ℝ) * inner (𝕜 := ℝ) (z i) v,
    gradient proxy.energy z + blockEmbed i v)

theorem Data.reconstruct_eq_replacedOracle (d : Data N E) (i : Fin (N + 1))
    (hA : IsSelfAdjoint (d.A i)) (b : E) (z : BlockProduct (N + 1) E) :
    d.reconstruct i b (d.A i (z i)) z = ((d.censorGate i).replaceForce i b).blockOracle z := by
  let c := (d.censorGate i).replaceForce i b
  exact Prod.ext (c.eraseOperator_energy i z) (c.eraseOperator_gradient i hA z)

omit [CompleteSpace E] in
theorem Data.replaceForce_self (d : Data N E) (i : Fin (N + 1)) :
    d.replaceForce i (d.b i) = d := by
  simp [replaceForce, Function.update_eq_self]

theorem Data.reconstruct_eq_censoredOracle (d : Data N E) (i : Fin (N + 1))
    (hA : IsSelfAdjoint (d.A i)) (z : BlockProduct (N + 1) E) :
    d.reconstruct i (d.b i) (d.A i (z i)) z = (d.censorGate i).blockOracle z := by
  rw [d.reconstruct_eq_replacedOracle i hA]
  exact congrArg (fun c : Data N E => c.blockOracle z) ((d.censorGate i).replaceForce_self i)

/-- Before the preceding gate opens, the decoder may use zero (or any other
vector) instead of the still-hidden force vector. -/
theorem Data.reconstruct_unauthorized (d : Data N E) (j : Fin N)
    (hA : IsSelfAdjoint (d.A j.succ)) (b : E) {z : BlockProduct (N + 1) E}
    (hz : |radialReadout (d.a j.castSucc) d.B d.α (z j.castSucc)| ≤ 1 / 4) :
    d.reconstruct j.succ b (d.A j.succ (z j.succ)) z = (d.censorGate j.succ).blockOracle z := by
  rw [d.reconstruct_eq_replacedOracle j.succ hA]
  apply (d.censorGate j.succ).replaceForce_blockOracle_eq j b
  have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this
  simpa only [censorGate, Function.update_of_ne hne] using hz

/-- The first block is always authorized. A later block becomes authorized
exactly when its preceding readout leaves the fixed flat region. -/
noncomputable def Data.oracleAuthorized (d : Data N E) (i : Fin (N + 1))
    (z : BlockProduct (N + 1) E) : Bool :=
  Fin.cases true (fun j => decide (1 / 4 < |radialReadout (d.a j.castSucc) d.B d.α (z j.castSucc)|)) i

omit [CompleteSpace E] in
@[simp] theorem Data.oracleAuthorized_zero (d : Data N E) (z : BlockProduct (N + 1) E) :
    d.oracleAuthorized 0 z = true := rfl

omit [CompleteSpace E] in
@[simp] theorem Data.oracleAuthorized_succ (d : Data N E) (j : Fin N)
    (z : BlockProduct (N + 1) E) :
    d.oracleAuthorized j.succ z = true ↔
      1 / 4 < |radialReadout (d.a j.castSucc) d.B d.α (z j.castSucc)| := by
  simp [oracleAuthorized]

/-- On every query, the authorized-or-zero force vector together with one
matrix response reconstructs the same static censored oracle. -/
theorem Data.reconstruct_authorized_or_zero (d : Data N E) (i : Fin (N + 1))
    (hA : IsSelfAdjoint (d.A i)) (z : BlockProduct (N + 1) E) :
    d.reconstruct i (if d.oracleAuthorized i z = true then d.b i else 0)
      (d.A i (z i)) z = (d.censorGate i).blockOracle z := by
  by_cases ha : d.oracleAuthorized i z = true
  · simpa only [ha, if_true] using d.reconstruct_eq_censoredOracle i hA z
  · simp only [ha, if_false]
    revert hA ha
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _ ha
      exact (ha rfl).elim
    · intro hA ha
      exact d.reconstruct_unauthorized j hA 0 (le_of_not_gt (fun h => ha ((d.oracleAuthorized_succ j z).mpr h)))

/-- Before the current readout exits, this decoder is also the original,
uncensored function's exact first-order oracle. -/
theorem Data.reconstruct_true_oracle (d : Data N E) (i : Fin (N + 1))
    (hA : IsSelfAdjoint (d.A i)) {z : BlockProduct (N + 1) E}
    (hz : |radialReadout (d.a i) d.B d.α (z i)| ≤ 1 / 4) :
    d.reconstruct i (if d.oracleAuthorized i z = true then d.b i else 0)
      (d.A i (z i)) z = d.blockOracle z := by
  rw [d.reconstruct_authorized_or_zero i hA z, d.censorGate_blockOracle_eq i hz]

end RandomizedFO2003.Cascade
