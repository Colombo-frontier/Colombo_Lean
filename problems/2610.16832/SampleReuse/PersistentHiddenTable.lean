import SampleReuse.FiniteKernelBridge

/-! A hidden block and its biased reusable table are sampled jointly once.
Public adaptive requests ignore the hidden coordinate. The resulting law
equals the measurable hidden-disclosure kernel used by the stage bound. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {H S Key A : Type}

def liftPublicQuery (query : ∀ n, FiniteHistory S A n → Key)
    (n : ℕ) (h : FiniteHistory (H × S) A n) : Key := query n (finiteHistoryMapInitial Prod.snd n h)

theorem disclosureCache_liftPublic (query : ∀ n, FiniteHistory S A n → Key) :
    ∀ n (h : FiniteHistory (H × S) A n),
      disclosureCache (liftPublicQuery query) n h =
        disclosureCache query n (finiteHistoryMapInitial Prod.snd n h) := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    change Function.update (disclosureCache (liftPublicQuery query) n h.1)
      (query n (finiteHistoryMapInitial Prod.snd n h.1)) (some h.2) =
      Function.update (disclosureCache query n (finiteHistoryMapInitial Prod.snd n h.1))
        (query n (finiteHistoryMapInitial Prod.snd n h.1)) (some h.2)
    rw [ih]

variable [Fintype H] [Fintype S] [Fintype Key] [Fintype A]
  [MeasurableSpace H] [MeasurableSingletonClass H]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace Key] [MeasurableSingletonClass Key]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem seededDisclosureKernel_eq_hidden (query : ∀ n, FiniteHistory S A n → Key)
    (hq : ∀ n, Measurable (query n)) (p : H → Key → PMF A) (n : ℕ) :
    finitePMFKernel (seededDisclosurePMF (liftPublicQuery query) (fun s : H × S => p s.1) n) =
      hiddenDisclosureKernel query hq p n := by
  ext h : 1
  change (disclosurePMF
    (disclosureCache (liftPublicQuery query) n h (liftPublicQuery query n h))
    (p (finiteHistoryInitial n h).1 (liftPublicQuery query n h))).toMeasure = _
  rw [disclosureCache_liftPublic]
  rfl

theorem hidden_fixed_table_kernel_law (ρ : PMF H) (μ : PMF S)
    (query : ∀ n, FiniteHistory S A n → Key) (hq : ∀ n, Measurable (query n))
    (p : H → Key → PMF A) (n : ℕ) :
    (seededTablePMF (finiteProdPMF ρ μ) (fun s : H × S => p s.1)).toMeasure.map
      (fun z => tableHistory (liftPublicQuery query) z.1 z.2 n) =
      adaptiveKernelLaw (ρ.toMeasure.prod μ.toMeasure) (hiddenDisclosureKernel query hq p) n := by
  rw [seeded_table_kernel_law, finiteProdPMF_toMeasure]
  have he : (fun n => finitePMFKernel
      (seededDisclosurePMF (liftPublicQuery query) (fun s : H × S => p s.1) n)) =
      hiddenDisclosureKernel query hq p := funext (seededDisclosureKernel_eq_hidden query hq p)
  rw [he]

end
end SampleReuse
