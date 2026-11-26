import UpperProgramRegularization
import UpperProgramExecution
import OracleSemantics

/-! Measurability of the actual finite adaptive run under the exact sample model. -/

open MeasureTheory MeasureTheory.Measure

namespace Task006.Full

namespace PairedQueryProgram

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

theorem runPrefix_succ_paired (P : PairedQueryProgram d N S) (F : Space d → Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) {k : ℕ} (hk : k < N) :
    P.toAlgorithm.runPrefix F tape seed (k + 1) =
      Function.update (P.toAlgorithm.runPrefix F tape seed k) ⟨k, hk⟩
        (F (P.point ⟨k, hk⟩ seed (P.toAlgorithm.runPrefix F tape seed k)) (tape (k / 2))) := by
  rw [OracleAlgorithm.runPrefix, dif_pos hk]
  rfl

theorem runPrefix_measurable (P : PairedQueryProgram d N S) (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (k : ℕ) :
    Measurable (fun w : S × (ℕ → Ω) => P.toAlgorithm.runPrefix F w.2 w.1 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hk : k < N
    · have hp : Measurable (fun w : S × (ℕ → Ω) =>
          P.point ⟨k, hk⟩ w.1 (P.toAlgorithm.runPrefix F w.2 w.1 k)) :=
        (P.point_measurable ⟨k, hk⟩).comp (measurable_fst.prodMk ih)
      have ht : Measurable (fun w : S × (ℕ → Ω) => w.2 (k / 2)) :=
        (measurable_pi_apply (k / 2)).comp measurable_snd
      have hr := hF.comp (hp.prodMk ht)
      have hstep : (fun w : S × (ℕ → Ω) => P.toAlgorithm.runPrefix F w.2 w.1 (k + 1)) =
          fun w => Function.update (P.toAlgorithm.runPrefix F w.2 w.1 k) ⟨k, hk⟩
            (F (P.point ⟨k, hk⟩ w.1 (P.toAlgorithm.runPrefix F w.2 w.1 k)) (w.2 (k / 2))) :=
        funext (fun w => P.runPrefix_succ_paired F w.2 w.1 hk)
      rw [hstep]
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = ⟨k, hk⟩
      · subst i
        simpa only [Function.update_self, Function.comp_def, Function.uncurry] using hr
      · simpa only [Function.update_of_ne hi, Function.comp_def]
          using (measurable_pi_apply i).comp ih
    · simpa only [OracleAlgorithm.runPrefix, dif_neg hk] using ih

theorem realizedOutput_measurable (P : PairedQueryProgram d N S) (F : Space d → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (P.toAlgorithm.realizedOutput F) :=
  P.postprocess_measurable.comp (measurable_fst.prodMk (P.runPrefix_measurable F hF N))

/-- Pointwise agreement simultaneously on all legal queries propagates through
the actual adaptive transcript, even though each next query uses earlier values. -/
theorem runPrefix_congr (P : PairedQueryProgram d N S) (R : ℝ)
    (hq : ∀ n seed h, P.point n seed h ∈ queryDomain d R)
    (F F' : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : S)
    (hF : ∀ handle x, x ∈ queryDomain d R → F x (tape handle) = F' x (tape handle)) (k : ℕ) :
    P.toAlgorithm.runPrefix F tape seed k = P.toAlgorithm.runPrefix F' tape seed k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < N
    · rw [P.runPrefix_succ_paired F tape seed hk, P.runPrefix_succ_paired F' tape seed hk]
      rw [ih, hF _ _ (hq _ _ _)]
    · simpa only [OracleAlgorithm.runPrefix, dif_neg hk] using ih

end PairedQueryProgram

theorem iid_all_handles_property {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → Prop} (hp : ∀ᵐ ω ∂μ, p ω) :
    ∀ᵐ tape ∂iidHandleLaw μ, ∀ handle, p (tape handle) := by
  apply ae_all_iff.mpr
  intro handle
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) handle).quasiMeasurePreserving.ae hp

/-- Actual output measurability follows from the given a.e. sample Lipschitz
condition. It does not require globally jointly measurable original samples. -/
theorem upperProgram_output_aestronglyMeasurable {d T : ℕ}
    (P : UpperProgramParameters) (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {L : ℝ}
    (I : SampleInstance d L P.R Ω μ) :
    AEStronglyMeasurable ((upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample)
      ((upperSeedLaw d T).prod (iidHandleLaw μ)) := by
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  obtain ⟨F, hFm, hFae⟩ := I.exists_joint_regularization hR
  have hm := (upperPairedProgram (T := T) P hd).realizedOutput_measurable F hFm
  have hTape := iid_all_handles_property μ hFae
  have hPair : ∀ᵐ w ∂(upperSeedLaw d T).prod (iidHandleLaw μ),
      ∀ handle x, x ∈ queryDomain d P.R → F x (w.2 handle) = I.sample x (w.2 handle) :=
    quasiMeasurePreserving_snd.ae hTape
  have heq : ((upperPairedProgram P hd).toAlgorithm.realizedOutput F) =ᵐ[
      (upperSeedLaw d T).prod (iidHandleLaw μ)]
      ((upperPairedProgram P hd).toAlgorithm.realizedOutput I.sample) := by
    filter_upwards [hPair] with w hw
    unfold OracleAlgorithm.realizedOutput OracleAlgorithm.finalTranscript
    rw [(upperPairedProgram (T := T) P hd).runPrefix_congr P.R
      (fun n s h => by
        change dist (upperQueryPoint P hd n s h) 0 ≤ 2 * P.R
        rw [dist_zero_right]
        linarith [upperQueryPoint_norm_le P hd n s h])
      F I.sample w.2 w.1 hw (upperReplyCount d T)]
  exact hm.aestronglyMeasurable.congr heq

#print axioms PairedQueryProgram.runPrefix_measurable
#print axioms upperProgram_output_aestronglyMeasurable

end Task006.Full
