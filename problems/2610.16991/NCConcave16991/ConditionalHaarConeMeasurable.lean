import NCConcave16991.ConditionalHaarConeOracle
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Borel reference value-plus-gradient replies with varying known data -/

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Haar

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

open ConePrimitives ConeRadial ConeClockGap ConeValue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : ℕ}

theorem radialClock_continuous {X : Type*} [TopologicalSpace X] {U : X → E}
    (hU : Continuous U) (q : ℝ) : Continuous (fun x ↦ radialClock q (U x)) :=
  (((continuous_const.add (hU.norm.pow 2)).sqrt).sub continuous_const).add
    ((hU.norm.pow 2).div_const (2 * q))

theorem variable_clock_continuous {X : Type*} [TopologicalSpace X] {V Z U : X → E}
    (hV : Continuous V) (hZ : Continuous Z) (hU : Continuous U) (q : ℝ) :
    Continuous (fun x ↦ clock q (V x) (Z x) (U x)) := by
  have hp : Continuous (fun x ↦ perpendicular (V x) (U x)) := hU.sub ((hU.inner hV).smul hV)
  have hH : Continuous (fun x ↦ latch ⟪zeta (Z x), V x⟫_ℝ) :=
    omega_contDiff.continuous.comp ((continuous_const.mul
      ((ConeSmooth.zeta_contDiff.continuous.comp hZ).inner hV)).sub continuous_const)
  have ha : Continuous (fun x ↦ ⟪U x, V x⟫_ℝ -
      Real.sqrt (1 + ‖perpendicular (V x) (U x)‖ ^ 2) + 4 * latch ⟪zeta (Z x), V x⟫_ℝ) :=
    ((hU.inner hV).sub ((continuous_const.add (hp.norm.pow 2)).sqrt)).add (continuous_const.mul hH)
  exact (radialClock_continuous hU q).sub (continuous_const.mul (theta_contDiff.continuous.comp ha))

theorem variable_gate_continuous {X : Type*} [TopologicalSpace X] {V U : X → E}
    (hV : Continuous V) (hU : Continuous U) (q : ℝ) :
    Continuous (fun x ↦ exitGate q (V x) (U x)) := by
  have hp : Continuous (fun x ↦ perpendicular (V x) (U x)) := hU.sub ((hU.inner hV).smul hV)
  have ha : Continuous (fun x ↦ (⟪U x, V x⟫_ℝ -
      Real.sqrt (q ^ 2 + ‖perpendicular (V x) (U x)‖ ^ 2)) / q) :=
    ((hU.inner hV).sub ((continuous_const.add (hp.norm.pow 2)).sqrt)).div_const q
  exact omega_contDiff.continuous.comp (ha.sub continuous_const)

abbrev ConeReferenceParameters (E : Type*) (M : ℕ) :=
  (Fin (M + 1) → E) × (Fin (M + 1) → E)

/-- Joint continuity holds also in the varying means and queried source rows,
so those parameters may be measurable functions of a transcript. -/
theorem referenceJointComponent_family_continuous (n : ℕ) (R q : ℝ) (frontier : ℕ) :
    Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦
      referenceJointComponent n R q frontier p.1.1 p.1.2 p.2) := by
  have hv (j : Fin (M + 1)) : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦ p.1.1 j) :=
    (continuous_apply j).comp continuous_fst.fst
  have hr (j : Fin (M + 1)) : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦ p.1.2 j) :=
    (continuous_apply j).comp continuous_fst.snd
  have hz (j : Fin (M + 1)) : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦ p.2.fst.fst j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      ((WithLp.fstL 2 ℝ (Blocks E M) (Blocks E M)).comp
        (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M)))).continuous.comp continuous_snd
  have hu (j : Fin (M + 1)) : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦ p.2.fst.snd j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      ((WithLp.sndL 2 ℝ (Blocks E M) (Blocks E M)).comp
        (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M)))).continuous.comp continuous_snd
  have hy (j : Fin (M + 1)) : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦ p.2.snd j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      (WithLp.sndL 2 ℝ (PrimalBlocks E M) (Blocks E M))).continuous.comp continuous_snd
  have hc : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦
      referenceClockGuard q frontier p.1.1 p.2.fst.fst p.2.fst.snd) := by
    apply continuous_finset_sum
    intro j hj
    by_cases hf : j.val < frontier
    · simpa only [if_pos hf, Function.comp_apply] using ((variable_clock_continuous (hv j) (hz j) (hu j) q).fun_add
        ((guard_contDiff 3000).continuous.comp (hz j)))
    · simpa only [if_neg hf, Function.comp_apply] using ((radialClock_continuous (hu j) q).fun_add
        ((guard_contDiff 3000).continuous.comp (hz j)))
  have hg (j : Fin (M + 1)) : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦
      previousGate q p.1.1 (fun l ↦ p.2.fst.snd l) j) := by
    unfold previousGate
    split
    · exact continuous_const
    · exact variable_gate_continuous (hv _) (hu _) q
  have hs : Continuous (fun p : ConeReferenceParameters E M × JointBlocks E M ↦
      ∑ j : Fin (M + 1), if j.val ≤ frontier then previousGate q p.1.1 (fun l ↦ p.2.fst.snd l) j *
        ⟪zeta (p.2.fst.fst j) - Real.sqrt (n : ℝ) • p.1.2 j, p.2.snd j⟫_ℝ else 0) := by
    apply continuous_finset_sum
    intro j hj
    by_cases hf : j.val ≤ frontier
    · simpa only [if_pos hf, Function.comp_apply] using (hg j).fun_mul
        (((ConeSmooth.zeta_contDiff.continuous.comp (hz j)).fun_sub (continuous_const.fun_smul (hr j))).inner (hy j))
    · simpa only [if_neg hf] using (continuous_const : Continuous
        (fun _ : ConeReferenceParameters E M × JointBlocks E M ↦ (0 : ℝ)))
  exact hc.fun_add (continuous_const.fun_mul hs)

theorem referenceFlatComponent_family_continuous (n : ℕ) (R q : ℝ) (frontier : ℕ) :
    Continuous (fun p : ConeReferenceParameters E M ×
      JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) ↦
      referenceFlatComponent n R q frontier p.1.1 p.1.2 p.2) := by
  unfold referenceFlatComponent
  let Φ : ConeReferenceParameters E M ×
      JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) →
      ConeReferenceParameters E M × JointBlocks E M :=
    fun p ↦ (p.1, (ConeProblem.jointCoordinates E M).symm p.2)
  have hΦ : Continuous Φ := continuous_fst.prodMk
    ((ConeProblem.jointCoordinates E M).symm.continuous.comp continuous_snd)
  exact ((referenceJointComponent_family_continuous (E := E) (M := M) n R q frontier).comp hΦ).congr
    (fun p ↦ rfl)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The reference full gradient is Borel in both known data and the query,
proved from the actual derivative, rather than specified by an oracle axiom. -/
theorem referenceFlatComponent_gradient_measurable (n : ℕ) (R q : ℝ) (frontier : ℕ) :
    Measurable (fun p : ConeReferenceParameters E M ×
      JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) ↦
      gradient (referenceFlatComponent n R q frontier p.1.1 p.1.2) p.2) := by
  have hd : Measurable (fun p : ConeReferenceParameters E M ×
      JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) ↦
      fderiv ℝ (referenceFlatComponent n R q frontier p.1.1 p.1.2) p.2) :=
    measurable_fderiv_with_param ℝ
      (f := fun p : ConeReferenceParameters E M ↦ referenceFlatComponent n R q frontier p.1 p.2)
      (referenceFlatComponent_family_continuous (E := E) (M := M) n R q frontier)
  exact (InnerProductSpace.toDual ℝ
    (JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M))).symm.continuous.measurable.comp hd

theorem referenceResponse_measurable (n : ℕ) (R q : ℝ) (frontier : ℕ) :
    Measurable (fun p : ConeReferenceParameters E M ×
      JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M) ↦
      (referenceFlatComponent n R q frontier p.1.1 p.1.2 p.2,
        (gradient (referenceFlatComponent n R q frontier p.1.1 p.1.2) p.2).fst,
        (gradient (referenceFlatComponent n R q frontier p.1.1 p.1.2) p.2).snd)) := by
  have hv := (referenceFlatComponent_family_continuous (E := E) (M := M) n R q frontier).measurable
  have hg := referenceFlatComponent_gradient_measurable (E := E) (M := M) n R q frontier
  have hz := (WithLp.fstL 2 ℝ
    (PrimalSpace (ConeProblem.primalDimension E M)) (DualSpace (ConeProblem.dualDimension E M))).continuous.measurable.comp hg
  have hu := (WithLp.sndL 2 ℝ
    (PrimalSpace (ConeProblem.primalDimension E M)) (DualSpace (ConeProblem.dualDimension E M))).continuous.measurable.comp hg
  exact hv.prodMk (hz.prodMk hu)

end

end NCConcave16991.Haar
