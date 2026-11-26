import HeavyTail.ChangingHistoryKernel
import HeavyTail.AdaptiveKernelConcentration

/-! Law-preserving modification of history kernels on exceptional histories.
No measurability assumption on the predicate defining the exceptional set is
needed: a measurable null envelope supplies the modification set. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

namespace HeavyTail.AdaptiveKernel
universe u
variable {Seed Reply : Type u} [MeasurableSpace Seed] [MeasurableSpace Reply]

theorem exists_measurable_full_set {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {p : Ω → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∃ s : Set Ω, MeasurableSet s ∧ (∀ᵐ x ∂μ, x ∈ s) ∧ ∀ x ∈ s, p x := by
  obtain ⟨t, hsub, ht, hzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨tᶜ, ht.compl, ?_, ?_⟩
  · apply ae_iff.mpr
    simpa using hzero
  · intro x hx
    exact Classical.byContradiction fun hn ↦ hx (hsub hn)

theorem changingHistoryLaw_congr_ae (P : Measure Seed)
    (κ κ' : (t : ℕ) → Kernel (History Seed Reply t) Reply)
    [∀ t, IsMarkovKernel (κ t)] [∀ t, IsMarkovKernel (κ' t)]
    (h : ∀ t, κ t =ᵐ[changingHistoryLaw P κ t] κ' t) (n : ℕ) :
    changingHistoryLaw P κ n = changingHistoryLaw P κ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [changingHistoryLaw]
    rw [← ih]
    exact Measure.compProd_congr (h n)

theorem changingHistorySum_congr_ae (P : Measure Seed)
    (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply)
    [∀ t, IsMarkovKernel (κ t)]
    (F G : (t : ℕ) → History Seed Reply t × Reply → ℝ)
    (hF : ∀ t, Measurable (F t)) (hG : ∀ t, Measurable (G t))
    (h : ∀ t, ∀ᵐ x ∂changingHistoryLaw P κ t, ∀ r, F t (x, r) = G t (x, r)) (n : ℕ) :
    historySum F n =ᵐ[changingHistoryLaw P κ n] historySum G n := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ ↦ rfl
  | succ n ih =>
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (historySum_measurable hF (n + 1))
        (historySum_measurable hG (n + 1)))
    filter_upwards [ih, h n] with x hx hr
    exact Filter.Eventually.of_forall fun r ↦ by
      simp only [historySum, hx, hr r]

end HeavyTail.AdaptiveKernel
