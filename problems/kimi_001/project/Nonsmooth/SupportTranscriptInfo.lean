import Nonsmooth.AugmentedSupport
import Nonsmooth.ConditionalMean

open MeasureTheory
open scoped InnerProductSpace
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

def supportTranscriptInformation (p : Policy Ω S E) (ω : Ω) (n : ℕ) : MeasurableSpace (Fin k → E) :=
  MeasurableSpace.comap (fun a => supportAugmentedTranscript p a ω n) inferInstance

theorem supportTranscriptInformation_le (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    supportTranscriptInformation (k := k) p ω n ≤ (inferInstance : MeasurableSpace (Fin k → E)) :=
  measurable_iff_comap_le.mp ((supportAugmentedTranscript_measurable p hp n).comp
    (measurable_id.prodMk measurable_const))

theorem supportTranscriptInformation_zero (p : Policy Ω S E) (ω : Ω) :
    supportTranscriptInformation (k := k) p ω 0 = ⊥ := by
  exact MeasurableSpace.comap_const Fin.elim0

theorem supportTranscriptInformation_le_succ (p : Policy Ω S E) (ω : Ω) (n : ℕ) :
    supportTranscriptInformation (k := k) p ω n ≤ supportTranscriptInformation p ω (n + 1) := by
  letI : MeasurableSpace (Fin k → E) := supportTranscriptInformation p ω (n + 1)
  have hh : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω (n + 1)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hi : Measurable (Fin.init : SupportHistory E k (n + 1) → SupportHistory E k n) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)
  have h := measurable_iff_comap_le.mp (hi.comp hh)
  convert! h using 1 <;>
    simp only [Function.comp_def, supportAugmentedTranscript, Fin.init_snoc,
      supportTranscriptInformation]

theorem supportTranscriptInformation_mono (p : Policy Ω S E) (ω : Ω) :
    Monotone (supportTranscriptInformation (k := k) p ω) :=
  monotone_nat_of_le_succ (supportTranscriptInformation_le_succ p ω)

theorem support_run_transcript_measurable (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    @Measurable (Fin k → E) S (supportTranscriptInformation p ω n) inferInstance
      (fun a => p.run (finiteSupport a) ω n) := by
  letI : MeasurableSpace (Fin k → E) := supportTranscriptInformation p ω n
  have hh : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    measurable_iff_comap_le.mpr le_rfl
  have hs := (stateOnHistory_measurable hp n).comp
    ((measurable_const (a := ω)).prodMk ((supportEraseHistory_measurable n).comp hh))
  simpa only [Function.comp_def, supportAugmentedTranscript_state] using hs

theorem support_output_transcript_measurable (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    @Measurable (Fin k → E) E (supportTranscriptInformation p ω n) inferInstance
      (fun a => p.result (finiteSupport a) ω n) := by
  letI : MeasurableSpace (Fin k → E) := supportTranscriptInformation p ω n
  exact hp.output.comp (measurable_const.prodMk (support_run_transcript_measurable p hp ω n))

theorem support_query_transcript_measurable (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    @Measurable (Fin k → E) E (supportTranscriptInformation p ω n) inferInstance
      (fun a => p.query n ω (p.run (finiteSupport a) ω n)) := by
  letI : MeasurableSpace (Fin k → E) := supportTranscriptInformation p ω n
  exact (hp.query n).comp (measurable_const.prodMk (support_run_transcript_measurable p hp ω n))

end
end Nonsmooth
