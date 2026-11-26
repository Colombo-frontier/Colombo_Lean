import RandomizedFO2003.CascadeFunction

namespace RandomizedFO2003.Cascade

open Primitives
open scoped BigOperators Topology

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Removing one outgoing gate means replacing only its direction by zero.
The last block is allowed: its readout is not an outgoing energy term. -/
noncomputable def Data.censorGate (d : Data N E) (i : Fin (N + 1)) : Data N E :=
  { d with a := Function.update d.a i 0 }

noncomputable def Data.replaceForce (d : Data N E) (i : Fin (N + 1)) (b : E) : Data N E :=
  { d with b := Function.update d.b i b }

theorem Data.censorGate_gate (d : Data N E) (i j : Fin (N + 1)) (x : E) :
    (d.censorGate i).gate j x = if j = i then 0 else d.gate j x := by
  by_cases hji : j = i
  · subst j
    simp only [censorGate, Data.gate, Function.update_self, if_true,
      radialGate, radialReadout, inner_zero_left, zero_div]
    exact gate_zero_of_le (by norm_num)
  · simp only [censorGate, Data.gate, Function.update_of_ne hji, if_neg hji]

theorem Data.censorGate_energy_eq (d : Data N E) (i : Fin (N + 1))
    (z : BlockProduct (N + 1) E) (hz : d.gate i (z i) = 0) :
    (d.censorGate i).energy z = d.energy z := by
  have hg (j : Fin N) : (d.censorGate i).gate j.castSucc (z j.castSucc) = d.gate j.castSucc (z j.castSucc) := by
    rw [d.censorGate_gate]
    split_ifs with hji
    · subst i
      exact hz.symm
    · rfl
  simp only [Data.energy, show (d.censorGate i).A = d.A from rfl,
    show (d.censorGate i).force = d.force from rfl, hg]

/-- At a flat readout the original and censored functions agree on a full
neighborhood in the block space, not just in value at one point. -/
theorem Data.censorGate_energy_eventuallyEq (d : Data N E) (i : Fin (N + 1))
    {z : BlockProduct (N + 1) E} (hz : |radialReadout (d.a i) d.B d.α (z i)| ≤ 1 / 4) :
    (d.censorGate i).energy =ᶠ[𝓝 z] d.energy := by
  have hg := (radialGate_eventually_zero (d.a i) d.B d.α hz).comp_tendsto
    (blockProjection (E := E) (N + 1) i).continuous.continuousAt
  filter_upwards [hg] with x hx
  exact d.censorGate_energy_eq i x hx

/-- A later block's right-hand vector appears only multiplied by the
preceding gate. If that gate vanishes, its vector can be replaced arbitrarily. -/
theorem Data.replaceForce_energy_eq (d : Data N E) (j : Fin N) (b : E)
    (z : BlockProduct (N + 1) E) (hz : d.gate j.castSucc (z j.castSucc) = 0) :
    (d.replaceForce j.succ b).energy z = d.energy z := by
  have hf0 : (d.replaceForce j.succ b).force 0 (z 0) = d.force 0 (z 0) := by
    simp [replaceForce, Data.force, Ne.symm (Fin.succ_ne_zero j)]
  have hterm (k : Fin N) : d.gate k.castSucc (z k.castSucc) *
        (d.replaceForce j.succ b).force k.succ (z k.succ) =
      d.gate k.castSucc (z k.castSucc) * d.force k.succ (z k.succ) := by
    by_cases hkj : k = j
    · subst k
      simp only [hz, zero_mul]
    · have hne : k.succ ≠ j.succ := fun h => hkj (Fin.succ_inj.mp h)
      simp only [replaceForce, Data.force, Function.update_of_ne hne]
  simp only [Data.energy, show (d.replaceForce j.succ b).A = d.A from rfl,
    show (d.replaceForce j.succ b).gate = d.gate from rfl, hf0, hterm]

theorem Data.replaceForce_energy_eventuallyEq (d : Data N E) (j : Fin N) (b : E)
    {z : BlockProduct (N + 1) E} (hz : |radialReadout (d.a j.castSucc) d.B d.α (z j.castSucc)| ≤ 1 / 4) :
    (d.replaceForce j.succ b).energy =ᶠ[𝓝 z] d.energy := by
  have hg := (radialGate_eventually_zero (d.a j.castSucc) d.B d.α hz).comp_tendsto
    (blockProjection (E := E) (N + 1) j.castSucc).continuous.continuousAt
  filter_upwards [hg] with x hx
  exact d.replaceForce_energy_eq j b x hx

variable [CompleteSpace E]

noncomputable def Data.blockOracle (d : Data N E) (z : BlockProduct (N + 1) E) :
    ℝ × BlockProduct (N + 1) E := (d.energy z, gradient d.energy z)

theorem Data.blockOracle_eq_of_eventuallyEq (d d' : Data N E) {z : BlockProduct (N + 1) E}
    (h : d.energy =ᶠ[𝓝 z] d'.energy) : d.blockOracle z = d'.blockOracle z :=
  Prod.ext h.self_of_nhds h.gradient_eq

theorem Data.censorGate_blockOracle_eq (d : Data N E) (i : Fin (N + 1))
    {z : BlockProduct (N + 1) E} (hz : |radialReadout (d.a i) d.B d.α (z i)| ≤ 1 / 4) :
    (d.censorGate i).blockOracle z = d.blockOracle z :=
  (d.censorGate i).blockOracle_eq_of_eventuallyEq d (d.censorGate_energy_eventuallyEq i hz)

theorem Data.replaceForce_blockOracle_eq (d : Data N E) (j : Fin N) (b : E)
    {z : BlockProduct (N + 1) E} (hz : |radialReadout (d.a j.castSucc) d.B d.α (z j.castSucc)| ≤ 1 / 4) :
    (d.replaceForce j.succ b).blockOracle z = d.blockOracle z :=
  (d.replaceForce j.succ b).blockOracle_eq_of_eventuallyEq d (d.replaceForce_energy_eventuallyEq j b hz)

end RandomizedFO2003.Cascade
