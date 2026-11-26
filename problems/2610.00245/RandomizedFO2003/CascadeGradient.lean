import RandomizedFO2003.CascadeFunction

namespace RandomizedFO2003.Cascade

open Primitives Calculus
open scoped BigOperators

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def Data.forceGradient (d : Data N E) (i : Fin (N + 1)) (x : E) : E :=
  saturationSlope d.K (forcingReadout (d.b i) d.D x) • d.b i

noncomputable def Data.gateGradient (d : Data N E) (i : Fin (N + 1)) (x : E) : E :=
  (deriv Primitives.gate (radialReadout (d.a i) d.B d.α x) / d.α) •
    (fderiv ℝ (radialSquash d.B : E → E) x).adjoint (d.a i)

theorem Data.force_hasGradientAt (d : Data N E) (hD : d.D ≠ 0) (i : Fin (N + 1)) (x : E) :
    HasGradientAt (d.force i) (d.forceGradient i x) x :=
  forcing_hasGradientAt _ hD _ _ _

theorem Data.gate_hasGradientAt (d : Data N E) (i : Fin (N + 1)) (x : E) :
    HasGradientAt (d.gate i) (d.gateGradient i x) x := radialGate_hasGradientAt _ _ _ _

/-- The full gradient is derived from the exact scalar function by addition,
products, and coordinate pullbacks. No block-gradient formula is assumed. -/
theorem Data.energy_hasGradientAt (d : Data N E) (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : d.D ≠ 0)
    (z : BlockProduct (N + 1) E) : HasGradientAt d.energy
      ((∑ i : Fin (N + 1), blockEmbed i (d.A i (z i))) - blockEmbed 0 (d.forceGradient 0 (z 0)) -
        ∑ j : Fin N,
          (d.gate j.castSucc (z j.castSucc) • blockEmbed j.succ (d.forceGradient j.succ (z j.succ)) +
            d.force j.succ (z j.succ) • blockEmbed j.castSucc (d.gateGradient j.castSucc (z j.castSucc)))) z := by
  apply hasGradientAt_sub
  · apply hasGradientAt_sub
    · apply hasGradientAt_sum
      intro i _hi
      exact hasGradientAt_block i z (quadratic_hasGradientAt (d.A i) (hA i) (z i))
    · exact hasGradientAt_block 0 z (d.force_hasGradientAt hD 0 (z 0))
  · apply hasGradientAt_sum
    intro j _hj
    exact hasGradientAt_mul
      (hasGradientAt_block j.castSucc z (d.gate_hasGradientAt j.castSucc (z j.castSucc)))
      (hasGradientAt_block j.succ z (d.force_hasGradientAt hD j.succ (z j.succ)))

/-- The coordinate gradient includes only its incoming and outgoing edge,
including the first and last block conventions. -/
theorem Data.energy_gradient_apply (d : Data N E) (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : d.D ≠ 0)
    (z : BlockProduct (N + 1) E) (i : Fin (N + 1)) :
    gradient d.energy z i = d.A i (z i) - d.incoming z i • d.forceGradient i (z i) -
      d.outgoing z i • d.gateGradient i (z i) := by
  have hin : blockEmbed 0 (d.forceGradient 0 (z 0)) i +
      Fin.cases 0 (fun j : Fin N => d.gate j.castSucc (z j.castSucc) • d.forceGradient j.succ (z j.succ)) i =
      d.incoming z i • d.forceGradient i (z i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [blockEmbed_apply, Fin.succ_ne_zero]
  have hout : Fin.lastCases 0
      (fun j : Fin N => d.force j.succ (z j.succ) • d.gateGradient j.castSucc (z j.castSucc)) i =
      d.outgoing z i • d.gateGradient i (z i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  rw [(d.energy_hasGradientAt hA hD z).gradient]
  simp only [Finset.sum_add_distrib, ← blockEmbed_smul]
  simp only [PiLp.sub_apply, PiLp.add_apply, sum_blockEmbed_apply,
    sum_blockEmbed_succ_apply, sum_blockEmbed_castSucc_apply]
  rw [hout, ← hin]
  abel

theorem Data.energy_gradient_identity_region (d : Data N E)
    (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : d.D ≠ 0) (hB : 0 < d.B)
    (z : BlockProduct (N + 1) E) (i : Fin (N + 1)) (hz : ‖z i‖ ≤ d.B) :
    gradient d.energy z i = d.A i (z i) -
      (d.incoming z i * saturationSlope d.K (forcingReadout (d.b i) d.D (z i))) • d.b i -
      (d.outgoing z i * deriv Primitives.gate (inner (𝕜 := ℝ) (d.a i) (z i) / d.α) / d.α) • d.a i := by
  rw [d.energy_gradient_apply hA hD]
  simp only [Data.forceGradient, Data.gateGradient, radialSquash_fderiv_eq_id hB hz,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    radialReadout, radialSquash_eq_self hB hz, smul_smul, ← mul_div_assoc]

omit [CompleteSpace E] in
theorem Data.incoming_eq_one_of_gates (d : Data N E) (z : BlockProduct (N + 1) E)
    (hg : ∀ j : Fin N, d.gate j.castSucc (z j.castSucc) = 1) (i : Fin (N + 1)) :
    d.incoming z i = 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact hg j

/-- Once activation and the final linear saturation region have been proved,
the last block of the actual gradient is exactly the linear-system residual. -/
theorem Data.last_residual_eq_gradient (d : Data N E) (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : d.D ≠ 0)
    (z : BlockProduct (N + 1) E) (hg : ∀ j : Fin N, d.gate j.castSucc (z j.castSucc) = 1)
    (hq : |forcingReadout (d.b (Fin.last N)) d.D (z (Fin.last N))| ≤ d.K) :
    d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N) = gradient d.energy z (Fin.last N) := by
  rw [d.energy_gradient_apply hA hD, d.incoming_eq_one_of_gates z hg, d.outgoing_last]
  simp only [Data.forceGradient, saturationSlope_one hq, one_smul, zero_smul, sub_zero]

theorem Data.last_residual_norm_le (d : Data N E) (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : d.D ≠ 0)
    (z : BlockProduct (N + 1) E) (hg : ∀ j : Fin N, d.gate j.castSucc (z j.castSucc) = 1)
    (hq : |forcingReadout (d.b (Fin.last N)) d.D (z (Fin.last N))| ≤ d.K) :
    ‖d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N)‖ ≤ ‖gradient d.energy z‖ := by
  rw [d.last_residual_eq_gradient hA hD z hg hq]
  exact block_norm_le _ _

end RandomizedFO2003.Cascade
