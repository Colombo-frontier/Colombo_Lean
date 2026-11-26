import GradientHessian.RawHierarchy
import GradientHessian.HierarchyParameterMeasurable
import GradientHessian.HierarchyJointJets
import GradientHessian.HigherHierarchyDimension
import GradientHessian.ReadoutMeasurability

/-! All-state joint measurability of the literal presampled scalar and its
physical jets. The readout assembly is measurable even at a zero denominator;
no good-event or unit-vector assumption is imposed on these decoders. -/

noncomputable section
namespace GradientHessian.RawHierarchy
open Matrix LowRank HigherHierarchy HierarchyParameters JetLocality

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def coefficients (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : (t : ℕ) → Raw d n r J E H t →
      Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t
  | 0, x => (fun i => (matrixEuclideanMap (MatrixGoodSpectrum.sourceMatrix P J (x.1 i)),
      (fun j => InverseGate.H₀ • matrixEuclideanMap B (x.2.1 i j)),
      (fun j => SourceOperator.readoutVector J P (x.1 i) fallback (matrixEuclideanMap B (x.2.1 i j))),
      x.2.2.1 i), x.2.2.2)
  | t+1, x => (fun i => coefficients P B fallback t (x.1 i), x.2)

omit [∀ t, InnerProductSpace ℝ (H t)] [∀ t, NormedAddCommGroup (H t)] in
theorem decode_coefficients (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (x : Raw d n r J E H t),
    decode t (coefficients P B fallback t x) = assemble P B fallback t x
  | 0, _ => rfl
  | t+1, x => by
    change HigherHierarchy.StepData.mk (fun i => decode t (coefficients P B fallback t (x.1 i))) x.2 =
      HigherHierarchy.StepData.mk (fun i => assemble P B fallback t (x.1 i)) x.2
    congr 1
    funext i
    exact decode_coefficients P B fallback t (x.1 i)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ t, MeasurableSpace (H t)] [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]

theorem readoutVector_measurable {T : Type*} [MeasurableSpace T]
    (P : Matrix (Fin d) (Fin d) ℝ) (fallback : Fin d → ℝ)
    {X : T → Matrix (Fin d) (Fin n) ℝ} {w : T → EuclideanSpace ℝ (Fin d)}
    (hX : Measurable X) (hw : Measurable w) :
    Measurable (fun x => SourceOperator.readoutVector J P (X x) fallback (w x)) := by
  have hv : Measurable (fun x => ⇑(w x)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).continuous.measurable.comp hw
  have hr := (ReadoutMeasurability.source_readout_joint_measurable J P fallback).comp (hX.prodMk hv)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.measurable.comp hr

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [FiniteDimensional ℝ E] [∀ t, BorelSpace (H t)] [∀ t, FiniteDimensional ℝ (H t)]
  [∀ t, InnerProductSpace ℝ (H t)] [∀ t, NormedAddCommGroup (H t)] in
theorem coefficients_measurable (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) :
    ∀ t, Measurable (coefficients (n := n) (J := J) (E := E) (H := H) P B fallback t)
  | 0 => by
    letI : MeasurableSpace ((EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin d)) := borel _
    letI : BorelSpace ((EuclideanSpace ℝ (Fin d)) →L[ℝ] EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
    have hX (i : Fin 8) : Measurable (fun x : Raw d n r J E H 0 => x.1 i) := by fun_prop
    have hw (i : Fin 8) (j : Fin (4096*J^2+1)) :
        Measurable (fun x : Raw d n r J E H 0 => matrixEuclideanMap B (x.2.1 i j)) :=
      (matrixEuclideanMap B).continuous.measurable.comp (by fun_prop)
    change Measurable (fun x : Raw d n r J E H 0 =>
      ((fun i => (matrixEuclideanMap (MatrixGoodSpectrum.sourceMatrix P J (x.1 i)),
        (fun j => InverseGate.H₀ • matrixEuclideanMap B (x.2.1 i j)),
        (fun j => SourceOperator.readoutVector J P (x.1 i) fallback (matrixEuclideanMap B (x.2.1 i j))),
        x.2.2.1 i)), x.2.2.2))
    apply Measurable.prodMk _ (by fun_prop)
    apply measurable_pi_lambda
    intro i
    apply Measurable.prodMk
      ((continuous_matrixEuclideanMap d d).measurable.comp
        ((ReadoutMeasurability.sourceMatrix_measurable P J).comp (hX i)))
    apply Measurable.prodMk
      (measurable_pi_lambda _ (fun j => measurable_const.smul (hw i j)))
    exact (measurable_pi_lambda _ (fun j => readoutVector_measurable P fallback (hX i) (hw i j))).prodMk
      (by fun_prop)
  | t+1 => by
    change Measurable (fun x : (Fin 8 → Raw d n r J E H t) × (Fin 8 → H t) =>
      ((fun i => coefficients P B fallback t (x.1 i)),x.2))
    exact (measurable_pi_lambda _ (fun i =>
      (coefficients_measurable P B fallback t).comp (by fun_prop))).prodMk measurable_snd

theorem scalar_joint_measurable (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) {K : ℝ} (hK : 0<K) (t : ℕ)
    [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
    [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)] :
    Measurable (fun p : Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      scalar K t (assemble P B fallback t p.1) p.2) := by
  have hc := ((scalarJoint_contDiff (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
    (m := 4096*J^2) hK t).continuous.measurable).comp
      (((coefficients_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def, scalarJoint, decode_coefficients] using hc

theorem outgoing_joint_measurable (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) {K : ℝ} (hK : 0<K) (t : ℕ)
    [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
    [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)] :
    Measurable (fun p : Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t =>
      outgoing K t (assemble P B fallback t p.1) p.2) := by
  have hc := ((outgoingJoint_contDiff (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
    (m := 4096*J^2) hK t).continuous.measurable).comp
      (((coefficients_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def, outgoingJoint, decode_coefficients] using hc

theorem richJet_joint_measurable (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) {K : ℝ} (hK : 0<K) (t : ℕ)
    [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
    [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)] :
    @Measurable (Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
        (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
          (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))
      inferInstance (borel _) (fun p => richJet (scalar K t (assemble P B fallback t p.1)) p.2) := by
  have hd := (richDecoder_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
    (m := 4096*J^2) hK t).borel_measurable
  have hm : @Measurable
      (Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t ×
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) _ inferInstance (borel _)
      (richDecoder K t) := hd.mono OpensMeasurableSpace.borel_le le_rfl
  have hc := hm.comp
    (((coefficients_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def, ← richJet_decode hK, decode_coefficients] using hc

theorem ordinaryJet_joint_measurable (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ) {K : ℝ} (hK : 0<K) (t : ℕ)
    [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
    [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)] :
    @Measurable (Raw d n r J E H t × Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
      inferInstance (borel _) (fun p => ordinaryJet (scalar K t (assemble P B fallback t p.1)) p.2) := by
  have hd := (ordinaryDecoder_continuous (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H)
    (m := 4096*J^2) hK t).borel_measurable
  have hm : @Measurable
      (Parameters (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t ×
        Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) _ inferInstance (borel _)
      (ordinaryDecoder K t) := hd.mono OpensMeasurableSpace.borel_le le_rfl
  have hc := hm.comp
    (((coefficients_measurable (n := n) (J := J) (E := E) (H := H) P B fallback t).comp measurable_fst).prodMk measurable_snd)
  simpa only [Function.comp_def, ← ordinaryJet_decode hK, decode_coefficients] using hc

end GradientHessian.RawHierarchy

