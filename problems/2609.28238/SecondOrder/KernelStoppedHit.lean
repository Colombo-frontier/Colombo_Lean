import SecondOrder.KernelFirstEntry

open MeasureTheory ProbabilityTheory
open scoped Classical

universe u
namespace SecondOrder
noncomputable section
variable {S A : Type u} [MeasurableSpace S] [MeasurableSpace A]

theorem kernelSurvivalSet_mono (safe safe' : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, safe n ⊆ safe' n) : ∀ n, kernelSurvivalSet safe n ⊆ kernelSurvivalSet safe' n := by
  intro n
  induction n with
  | zero => exact hs 0
  | succ n ih => intro h hh; exact ⟨hs (n+1) hh.1,ih hh.2⟩

theorem kernelBeforeSet_mono (safe safe' : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, safe n ⊆ safe' n) (n : ℕ) : kernelBeforeSet safe n ⊆ kernelBeforeSet safe' n := by
  cases n with
  | zero => exact Set.Subset.rfl
  | succ n => intro h hh; exact kernelSurvivalSet_mono safe safe' hs n hh

/-- A marked failure of a safety test, retained in all later histories.
The mark is inspected before the response at that time. -/
def kernelStoppedHitSet (safe hit : ∀ n, Set (FiniteHistory S A n)) :
    (n : ℕ) → Set (FiniteHistory S A n)
  | 0 => hit 0
  | n+1 => (Prod.fst ⁻¹' kernelStoppedHitSet safe hit n) ∪
      (kernelBeforeSet safe (n+1) ∩ hit (n+1))

theorem kernelStoppedHitSet_measurable (safe hit : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) (hh : ∀ n, MeasurableSet (hit n)) :
    ∀ n, MeasurableSet (kernelStoppedHitSet safe hit n) := by
  intro n
  induction n with
  | zero => exact hh 0
  | succ n ih =>
    exact (measurable_fst ih).union
      ((kernelBeforeSet_measurable safe hs (n+1)).inter (hh (n+1)))

theorem kernelStoppedHitSet_disjoint (safe hit : ∀ n, Set (FiniteHistory S A n))
    (hd : ∀ n, Disjoint (hit n) (safe n)) :
    ∀ n, Disjoint (kernelStoppedHitSet safe hit n) (kernelSurvivalSet safe n) := by
  intro n
  induction n with
  | zero => exact hd 0
  | succ n ih =>
    apply Set.disjoint_left.mpr
    intro h hm hs
    rcases hm with hm | hm
    · exact Set.disjoint_left.mp ih hm hs.2
    · exact Set.disjoint_left.mp (hd (n+1)) hm.2 hs.1

theorem kernelStoppedHitSet_subset_ever (safe hit : ∀ n, Set (FiniteHistory S A n)) :
    ∀ n, kernelStoppedHitSet safe hit n ⊆ (kernelSurvivalSet (fun k => (hit k)ᶜ) n)ᶜ := by
  intro n
  induction n with
  | zero => intro h hh hn; exact hn hh
  | succ n ih =>
    intro h hh hn
    rcases hh with hh | hh
    · exact ih hh hn.2
    · exact hn.1 hh.2

theorem kernelStoppedHit_probability_succ (μ : Measure S) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (FiniteHistory S A n) A) [∀ n, IsMarkovKernel (K n)]
    (safe hit : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) (hh : ∀ n, MeasurableSet (hit n))
    (hd : ∀ n, Disjoint (hit n) (safe n)) (n : ℕ) :
    (adaptiveKernelLaw μ K (n+1)).real (kernelStoppedHitSet safe hit (n+1)) =
      (adaptiveKernelLaw μ K n).real (kernelStoppedHitSet safe hit n)+
      (adaptiveKernelLaw μ K (n+1)).real (kernelBeforeSet safe (n+1) ∩ hit (n+1)) := by
  have hdis : Disjoint (Prod.fst ⁻¹' kernelStoppedHitSet safe hit n)
      (kernelBeforeSet safe (n+1) ∩ hit (n+1)) := by
    apply Set.disjoint_left.mpr
    intro h hx hy
    exact Set.disjoint_left.mp (kernelStoppedHitSet_disjoint safe hit hd n) hx hy.1
  rw [kernelStoppedHitSet,measureReal_union hdis
    ((kernelBeforeSet_measurable safe hs (n+1)).inter (hh (n+1)))]
  congr 1
  unfold Measure.real
  change ((adaptiveKernelLaw μ K n ⊗ₘ K n) (Prod.fst ⁻¹' kernelStoppedHitSet safe hit n)).toReal = _
  rw [←Measure.fst_apply (kernelStoppedHitSet_measurable safe hit hs hh n),Measure.fst_compProd]

/-- Agreement before either stopping cause transfers the marked cause
without charging the probability of the other cause as an error term. -/
theorem kernelStoppedHit_probability_eq (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe hit : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) (hh : ∀ n, MeasurableSet (hit n))
    (hd : ∀ n, Disjoint (hit n) (safe n))
    (heq : ∀ n h, h ∈ safe n → K n h=Q n h) :
    ∀ n, (adaptiveKernelLaw μ K n).real (kernelStoppedHitSet safe hit n)=
      (adaptiveKernelLaw μ Q n).real (kernelStoppedHitSet safe hit n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [kernelStoppedHit_probability_succ μ K safe hit hs hh hd n,
      kernelStoppedHit_probability_succ μ Q safe hit hs hh hd n,ih]
    congr 1
    have he := congrArg (fun η : Measure (FiniteHistory S A (n+1)) => η.real (hit (n+1)))
      (adaptiveKernelLaw_before_eq μ K Q safe hs heq (n+1))
    simpa only [measureReal_restrict_apply (hh (n+1)),Set.inter_comm] using he

theorem kernelStoppedHit_probability_le (μ : Measure S) [IsProbabilityMeasure μ]
    (K Q : ∀ n, Kernel (FiniteHistory S A n) A)
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (Q n)]
    (safe hit : ∀ n, Set (FiniteHistory S A n))
    (hs : ∀ n, MeasurableSet (safe n)) (hh : ∀ n, MeasurableSet (hit n))
    (hd : ∀ n, Disjoint (hit n) (safe n))
    (heq : ∀ n h, h ∈ safe n → K n h=Q n h) (N : ℕ) :
    (adaptiveKernelLaw μ K N).real (kernelStoppedHitSet safe hit N)≤
      (adaptiveKernelLaw μ Q N).real (kernelSurvivalSet (fun n => (hit n)ᶜ) N)ᶜ := by
  rw [kernelStoppedHit_probability_eq μ K Q safe hit hs hh hd heq N]
  exact measureReal_mono (kernelStoppedHitSet_subset_ever safe hit N)

end
end SecondOrder
