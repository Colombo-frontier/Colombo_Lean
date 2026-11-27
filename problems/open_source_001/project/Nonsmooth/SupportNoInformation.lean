import Nonsmooth.GaussianPosteriorEnergy

open MeasureTheory ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem finiteSupport_zero (a : Fin k → E) : finiteSupport a 0 = 0 := by
  simp [finiteSupport]

theorem supportWinner_zero (a : Fin k → E) : supportWinner a 0 = supportWinner (fun _ : Fin k => (0 : E)) 0 := by
  classical
  simp [supportWinner, finiteSupport_zero]

theorem supportAugmentedTranscript_observations (p : Policy Ω S E) (a : Fin k → E) (ω : Ω) (n : ℕ) :
    ∀ j : Fin n,
      (supportAugmentedTranscript p a ω n j).2.1 = supportWinner a (supportAugmentedTranscript p a ω n j).1 ∧
      (supportAugmentedTranscript p a ω n j).2.2 = finiteSupport a (supportAugmentedTranscript p a ω n j).1 := by
  induction n with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
    intro j
    refine Fin.lastCases ?_ (fun t => ?_) j
    · simp only [supportAugmentedTranscript, Fin.snoc_last, and_self]
    · simpa only [supportAugmentedTranscript, Fin.snoc_castSucc] using ih t

theorem supportAugmentedTranscript_succ_run (p : Policy Ω S E) (a : Fin k → E) (ω : Ω) (n : ℕ) :
    supportAugmentedTranscript p a ω (n + 1) =
      let x := p.query n ω (p.run (finiteSupport a) ω n)
      Fin.snoc (supportAugmentedTranscript p a ω n) (x, (supportWinner a x, finiteSupport a x)) := by
  simp only [supportAugmentedTranscript, supportAugmentedTranscript_state]

theorem supportTranscriptInformation_eq_of_extension (p : Policy Ω S E) (ω : Ω) (n : ℕ)
    (F : SupportHistory E k n → SupportHistory E k (n + 1)) (hF : Measurable F)
    (he : ∀ a : Fin k → E, supportAugmentedTranscript p a ω (n + 1) = F (supportAugmentedTranscript p a ω n)) :
    supportTranscriptInformation (k := k) p ω (n + 1) = supportTranscriptInformation p ω n := by
  apply le_antisymm ?_ (supportTranscriptInformation_le_succ p ω n)
  letI : MeasurableSpace (Fin k → E) := supportTranscriptInformation p ω n
  have hh : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    measurable_iff_comap_le.mpr le_rfl
  have heq : (fun a : Fin k → E => supportAugmentedTranscript p a ω (n + 1)) =
      F ∘ (fun a : Fin k → E => supportAugmentedTranscript p a ω n) := funext he
  exact measurable_iff_comap_le.mp (heq.symm ▸ hF.comp hh)

theorem supportTranscriptInformation_zero_query (p : Policy Ω S E) (ω : Ω) (n : ℕ)
    (hzero : ∀ a : Fin k → E, p.query n ω (p.run (finiteSupport a) ω n) = 0) :
    supportTranscriptInformation (k := k) p ω (n + 1) = supportTranscriptInformation p ω n := by
  let v : E × (Fin k × ℝ) := (0, (supportWinner (fun _ : Fin k => (0 : E)) 0, 0))
  let F : SupportHistory E k n → SupportHistory E k (n + 1) := fun h => Fin.snoc h v
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [F, Fin.snoc_last] using (measurable_const (a := v) : Measurable (fun _ : SupportHistory E k n => v))
    · simpa only [F, Fin.snoc_castSucc] using (measurable_pi_apply j : Measurable (fun h : SupportHistory E k n => h j))
  apply supportTranscriptInformation_eq_of_extension p ω n F hF
  intro a
  simp only [supportAugmentedTranscript_succ_run, hzero, supportWinner_zero, finiteSupport_zero]
  rfl

theorem supportTranscriptInformation_repeat_query (p : Policy Ω S E) (ω : Ω) (n : ℕ) (j : Fin n)
    (hrep : ∀ a : Fin k → E, p.query n ω (p.run (finiteSupport a) ω n) =
      (supportAugmentedTranscript p a ω n j).1) :
    supportTranscriptInformation (k := k) p ω (n + 1) = supportTranscriptInformation p ω n := by
  let F : SupportHistory E k n → SupportHistory E k (n + 1) := fun h => Fin.snoc h (h j)
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun t => ?_) i
    · simpa only [F, Fin.snoc_last] using (measurable_pi_apply j : Measurable (fun h : SupportHistory E k n => h j))
    · simpa only [F, Fin.snoc_castSucc] using (measurable_pi_apply t : Measurable (fun h : SupportHistory E k n => h t))
  apply supportTranscriptInformation_eq_of_extension p ω n F hF
  intro a
  rw [supportAugmentedTranscript_succ_run, hrep]
  have ho := supportAugmentedTranscript_observations p a ω n j
  simp only [← ho.1, ← ho.2]
  rfl

variable [Nontrivial E]

theorem gaussianSupportMean_zero_query (p : Policy Ω S E) (ω : Ω) (n : ℕ)
    (hzero : ∀ a : Fin k → E, p.query n ω (p.run (finiteSupport a) ω n) = 0) :
    gaussianSupportMean (k := k) p ω (n + 1) = gaussianSupportMean p ω n := by
  simp only [gaussianSupportMean, supportTranscriptInformation_zero_query p ω n hzero]

theorem gaussianSupportMean_repeat_query (p : Policy Ω S E) (ω : Ω) (n : ℕ) (j : Fin n)
    (hrep : ∀ a : Fin k → E, p.query n ω (p.run (finiteSupport a) ω n) =
      (supportAugmentedTranscript p a ω n j).1) :
    gaussianSupportMean (k := k) p ω (n + 1) = gaussianSupportMean p ω n := by
  simp only [gaussianSupportMean, supportTranscriptInformation_repeat_query p ω n j hrep]

end
end Nonsmooth
