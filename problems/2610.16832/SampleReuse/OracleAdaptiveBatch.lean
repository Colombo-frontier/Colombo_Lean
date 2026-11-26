import SampleReuse.OracleFreshness
import SampleReuse.OracleBatchSize

/-! Adaptive endpoints and adaptive integer batch sizes are chosen from the
past, before reading a reserved fresh iid block. All fixed-history accuracy
bounds here are supplied by the proved common-loss batch theorems. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

/-- A total implementation of prefix handles; within the reserved capacity
the handles are distinct. Values past the capacity are never used in the
accuracy theorems. -/
def prefixHandles {B : ℕ} (hB : 0 < B) (n : ℕ) (i : Fin n) : Fin B :=
  ⟨i.val % B, Nat.mod_lt _ hB⟩

theorem prefixHandles_injective {B n : ℕ} (hB : 0 < B) (hn : n ≤ B) :
    Function.Injective (prefixHandles hB n) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg Fin.val hij
  simpa only [prefixHandles, Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hn),
    Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt hn)] using he

def adaptiveBatchMean {Ω S E : Type*} [AddCommGroup E] [Module ℝ E]
    {B : ℕ} (hB : 0 < B) (A : S → Ω → E) (n : S → ℕ)
    (s : S) (block : SampleTape B Ω) : E :=
  batchMeanTape (A s) (prefixHandles hB (n s)) block

theorem adaptiveBatchMean_measurable {Ω S E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {B : ℕ} (hB : 0 < B)
    (A : S → Ω → E) (hA : Measurable (fun w : S × Ω => A w.1 w.2))
    (n : S → ℕ) (hn : Measurable n) :
    Measurable (fun w : S × SampleTape B Ω => adaptiveBatchMean hB A n w.1 w.2) := by
  have hk : ∀ k : ℕ, Measurable (fun w : S × SampleTape B Ω =>
      batchMeanTape (A w.1) (prefixHandles hB k) w.2) := by
    intro k
    exact (Finset.measurable_sum _ (fun i _ => hA.comp
      (measurable_fst.prodMk ((measurable_pi_apply (prefixHandles hB k i)).comp measurable_snd)))).const_smul _
  have hall : Measurable (fun w : (S × SampleTape B Ω) × ℕ =>
      batchMeanTape (A w.1.1) (prefixHandles hB w.2) w.1.2) :=
    measurable_from_prod_countable hk
  exact hall.comp (measurable_id.prodMk (hn.comp measurable_fst))

theorem adaptive_batch_error_bound {Ω S E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {H B : ℕ} (hB : 0 < B)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z₀ : Ω)
    (past : Finset (Fin H)) (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (reserved : Fin B → Fin H) (hfresh : ∀ i, reserved i ∉ past) (hinj : Function.Injective reserved)
    (A : S → Ω → E) (hA : Measurable (fun w : S × Ω => A w.1 w.2))
    (a : S → E) (ha : Measurable a) (n : S → ℕ) (hn : Measurable n)
    {η δ : ℝ} (hδ : 0 ≤ δ)
    (hfixed : ∀ s, (sampleTapeLaw B μ).real {block |
      η ≤ ‖adaptiveBatchMean hB A n s block - a s‖} ≤ δ) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖adaptiveBatchMean hB A n (history tape) (fun i => tape (reserved i)) - a (history tape)‖} ≤ δ := by
  let bad := {w : S × SampleTape B Ω | η ≤ ‖adaptiveBatchMean hB A n w.1 w.2 - a w.1‖}
  have hm : MeasurableSet bad := measurableSet_le measurable_const
    (((adaptiveBatchMean_measurable hB A hA n hn).sub (ha.comp measurable_fst)).norm)
  exact adaptive_fresh_event_real_bound μ z₀ past history hh hdep reserved hfresh hinj bad hm hδ hfixed

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {H B d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.adaptive_hessian_chord_confidence (h : Admissible μ P f F x₀)
    (hB : 0 < B) (z₀ : Ω) (past : Finset (Fin H))
    (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (reserved : Fin B → Fin H) (hfresh : ∀ i, reserved i ∉ past) (hinj : Function.Injective reserved)
    (x y : S → Point d) (hx : Measurable x) (hy : Measurable y)
    (n : S → ℕ) (hn : Measurable n) (hnpos : ∀ s, 0 < n s) (hncap : ∀ s, n s ≤ B)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hsize : ∀ s, 8 * (matrixMomentOrder (d + 1) δ : ℝ) *
      (2 * min P.hessianNoise (P.hessianLip * ‖x s-y s‖))^2 ≤ (n s : ℝ) * η^2) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖adaptiveBatchMean hB (fun s => hessianChordSample F (x s, y s)) n
        (history tape) (fun i => tape (reserved i)) -
          (hessian f (x (history tape)) - hessian f (y (history tape)))‖} ≤ δ := by
  have hA : Measurable (fun w : S × Ω => hessianChordSample F (x w.1, y w.1) w.2) :=
    (h.hessian_measurable.comp (measurable_snd.prodMk (hx.comp measurable_fst))).sub
      (h.hessian_measurable.comp (measurable_snd.prodMk (hy.comp measurable_fst)))
  have ha : Measurable (fun s => hessian f (x s) - hessian f (y s)) :=
    ((continuous_hessian h.population_smooth).measurable.comp hx).sub
      ((continuous_hessian h.population_smooth).measurable.comp hy)
  apply adaptive_batch_error_bound hB μ z₀ past history hh hdep reserved hfresh hinj
    _ hA _ ha n hn hδ.le
  intro s
  exact h.hessian_batch_confidence (x s) (y s) (prefixHandles hB (n s))
    (prefixHandles_injective hB (hncap s)) hη hδ (hnpos s) (hsize s)

theorem Admissible.adaptive_gradient_chord_confidence (h : Admissible μ P f F x₀)
    (hB : 0 < B) (z₀ : Ω) (past : Finset (Fin H))
    (history : SampleTape H Ω → S) (hh : Measurable history)
    (hdep : ∀ tape tape', (∀ r ∈ past, tape r = tape' r) → history tape = history tape')
    (reserved : Fin B → Fin H) (hfresh : ∀ i, reserved i ∉ past) (hinj : Function.Injective reserved)
    (x y : S → Point d) (hx : Measurable x) (hy : Measurable y)
    (n : S → ℕ) (hn : Measurable n) (hnpos : ∀ s, 0 < n s) (hncap : ∀ s, n s ≤ B)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hsize : ∀ s, 32 * (matrixMomentOrder (d + 1) δ : ℝ) *
      (2 * min P.gradientNoise (P.gradientLip * ‖x s-y s‖))^2 ≤ (n s : ℝ) * η^2) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖adaptiveBatchMean hB (fun s => gradientChordSample F (x s, y s)) n
        (history tape) (fun i => tape (reserved i)) -
          (gradient f (x (history tape)) - gradient f (y (history tape)))‖} ≤ δ := by
  have hA : Measurable (fun w : S × Ω => gradientChordSample F (x w.1, y w.1) w.2) :=
    (gradientChordSample_measurable F h.gradient_measurable).comp
      (((hx.comp measurable_fst).prodMk (hy.comp measurable_fst)).prodMk measurable_snd)
  have ha : Measurable (fun s => gradient f (x s) - gradient f (y s)) :=
    ((contDiff_gradient_one h.population_smooth).continuous.measurable.comp hx).sub
      ((contDiff_gradient_one h.population_smooth).continuous.measurable.comp hy)
  apply adaptive_batch_error_bound hB μ z₀ past history hh hdep reserved hfresh hinj
    _ hA _ ha n hn hδ.le
  intro s
  exact h.gradient_batch_confidence (x s) (y s) (prefixHandles hB (n s))
    (prefixHandles_injective hB (hncap s)) hη hδ (hnpos s) (hsize s)

end
end SampleReuse
