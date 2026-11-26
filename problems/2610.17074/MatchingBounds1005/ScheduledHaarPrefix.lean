import MatchingBounds1005.ChronologicalProjection
import MatchingBounds1005.GaussianStarts

/-! A closed finite-transcript event for every hidden prefix projection.
Closedness is proved through finite synthesis, so no measurability of a
random pseudoinverse or a random-rank projection is assumed. -/
noncomputable section
open scoped InnerProductSpace BigOperators
open MeasureTheory RandomizedFO2003.Rotations

namespace MatchingBounds1005.ScheduledHaar
universe u

def roundQueryTrace (E : Type) : (n : ℕ) → {H : Type u} →
    ActionHistory E (actionCount n) H → Fin n → E
  | 0, _, _ => Fin.elim0
  | n + 1, H, p => Fin.cons
      ((ActionHistory.seed E (actionCount n + 1) (H := (H × E) × E) p).2)
      (roundQueryTrace E n p)

theorem roundQueryTrace_measurable {E : Type} [MeasurableSpace E] (n : ℕ)
    {H : Type u} [MeasurableSpace H] :
    Measurable (roundQueryTrace E n (H := H)) := by
  apply measurable_pi_lambda
  intro i
  induction n generalizing H with
  | zero => exact i.elim0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (ActionHistory.seed_measurable (actionCount n + 1)).snd
      · exact ih j

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem RoundPolicy.selectQueries_eq (n : ℕ) {H : Type u} [MeasurableSpace H]
    (plan : RoundPolicy E n H) (Q : E →L[ℝ] E)
    (p : ActionHistory E (actionCount n) H) :
    (plan.compile Q n).selectQueries (actionCount n) p = List.ofFn (roundQueryTrace E n p) := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih =>
      simp only [RoundPolicy.compile, actionCount, ActionProgram.selectQueries,
        roundQueryTrace, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
      rw [ih plan.2]

end MatchingBounds1005.ScheduledHaar

namespace MatchingBounds1005.ScheduledPrefix
open ChronologicalProjection ScheduledHaar
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def maskedPrefix {n : ℕ} (xs : Fin n → E) (t : ℕ) (i : Fin n) : E :=
  if i.val ≤ t then xs i else 0

def synthesis {n : ℕ} (xs : Fin n → E) (t : ℕ) (c : Fin n → ℝ) : E :=
  ∑ i, c i • maskedPrefix xs t i

theorem continuous_synthesis {n : ℕ} (t : ℕ) (c : Fin n → ℝ) :
    Continuous (fun xs : Fin n → E => synthesis xs t c) := by
  apply continuous_finset_sum
  intro i _
  unfold maskedPrefix
  split_ifs
  · exact continuous_const.smul (continuous_apply i)
  · exact continuous_const

theorem maskedPrefix_span {n : ℕ} (xs : Fin n → E) (t : ℕ) :
    Submodule.span ℝ (Set.range (maskedPrefix xs t)) = prefixSpan (List.ofFn xs) (t + 1) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val ≤ t
    · rw [maskedPrefix, if_pos hi]
      apply Submodule.subset_span
      apply List.mem_take_iff_getElem.mpr
      refine ⟨i.val, by simp only [List.length_ofFn]; omega, ?_⟩
      simp
    · simp [maskedPrefix, hi]
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, hi, he⟩ := List.mem_take_iff_getElem.mp hx
    have hin : i < n := by simpa only [List.length_ofFn] using (lt_min_iff.mp hi).2
    have hit : i ≤ t := by omega
    have hx : maskedPrefix xs t ⟨i, hin⟩ = x := by
      simpa only [maskedPrefix, if_pos hit, List.getElem_ofFn] using he
    exact Submodule.subset_span ⟨⟨i, hin⟩, hx⟩

theorem mem_prefix_iff_synthesis {n : ℕ} (xs : Fin n → E) (t : ℕ) (v : E) :
    v ∈ prefixSpan (List.ofFn xs) (t + 1) ↔ ∃ c : Fin n → ℝ, synthesis xs t c = v := by
  rw [← maskedPrefix_span]
  exact Submodule.mem_span_range_iff_exists_fun ℝ

/-- A single closed event quantifies over every hidden direction and every
linear combination of every query prefix. -/
def prefixEvent {n : ℕ} (I : ℕ → Submodule ℝ E) (A : Submodule ℝ E) (η : ℝ) : Set (Fin n → E) :=
  {xs | ∀ t a, a ∈ A → a ∈ (I t)ᗮ → ∀ c : Fin n → ℝ,
    |⟪a, synthesis xs t c⟫_ℝ| ≤ 2 * η * ‖a‖ * ‖synthesis xs t c‖}

theorem isClosed_prefixEvent {n : ℕ} (I : ℕ → Submodule ℝ E) (A : Submodule ℝ E) (η : ℝ) :
    IsClosed (prefixEvent (n := n) I A η) := by
  unfold prefixEvent
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun t => isClosed_iInter (fun a => isClosed_iInter (fun _ =>
    isClosed_iInter (fun _ => isClosed_iInter (fun c =>
      isClosed_le (continuous_const.inner (continuous_synthesis t c)).abs
        (continuous_const.mul (continuous_synthesis t c).norm))))))

theorem prefixEvent_iff_projection {n : ℕ} (I : ℕ → Submodule ℝ E)
    (A : Submodule ℝ E) {η : ℝ} (hη : 0 ≤ η) (xs : Fin n → E) :
    xs ∈ prefixEvent I A η ↔ ∀ t a, a ∈ A → a ∈ (I t)ᗮ →
      ‖(prefixSpan (List.ofFn xs) (t + 1)).orthogonalProjection a‖ ≤ 2 * η * ‖a‖ := by
  constructor
  · intro hx t a ha hh
    let P := prefixSpan (List.ofFn xs) (t + 1)
    obtain ⟨c, hc⟩ := (mem_prefix_iff_synthesis xs t (P.orthogonalProjection a)).mp
      (P.orthogonalProjection a).property
    have hv := hx t a ha hh c
    rw [hc] at hv
    have he : ⟪a, (P.orthogonalProjection a : E)⟫_ℝ = ‖P.orthogonalProjection a‖ ^ 2 := by
      rw [← P.inner_orthogonalProjection_eq_of_mem_right (P.orthogonalProjection a) a]
      exact real_inner_self_eq_norm_sq _
    rw [he, abs_of_nonneg (sq_nonneg _)] at hv
    change ‖P.orthogonalProjection a‖ ^ 2 ≤ 2 * η * ‖a‖ * ‖P.orthogonalProjection a‖ at hv
    change ‖P.orthogonalProjection a‖ ≤ _
    have hn := norm_nonneg (P.orthogonalProjection a)
    have hb : 0 ≤ 2 * η * ‖a‖ := by positivity
    by_cases hz : ‖P.orthogonalProjection a‖ = 0
    · simpa only [hz] using hb
    · have hp : 0 < ‖P.orthogonalProjection a‖ := lt_of_le_of_ne hn (Ne.symm hz)
      nlinarith
  · intro hx t a ha hh c
    let P := prefixSpan (List.ofFn xs) (t + 1)
    have hv : synthesis xs t c ∈ P := (mem_prefix_iff_synthesis xs t _).mpr ⟨c, rfl⟩
    rw [← P.inner_orthogonalProjection_eq_of_mem_right ⟨synthesis xs t c, hv⟩ a]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hx t a ha hh) (norm_nonneg _))

theorem chronological_mem_prefixEvent {n : ℕ} (xs : Fin n → E)
    (I : ℕ → Submodule ℝ E) (A N : Submodule ℝ E)
    (hmono : ∀ t, I t ≤ I (t + 1)) (hc : ChronologicalIn I N (List.ofFn xs))
    (hIA : ∀ t, I t ≤ A) {η : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hangle : ∀ a ∈ A, ‖N.orthogonalProjection a‖ ≤ η * ‖a‖) :
    xs ∈ prefixEvent I A η :=
  (prefixEvent_iff_projection I A hη xs).mpr
    (hidden_prefix_bound (List.ofFn xs) I A N hmono hc hIA hη hηhalf hangle)

variable [MeasurableSpace E] [BorelSpace E]

theorem measurableSet_prefixEvent {n : ℕ} (I : ℕ → Submodule ℝ E) (A : Submodule ℝ E) (η : ℝ) :
    MeasurableSet (prefixEvent (n := n) I A η) := (isClosed_prefixEvent I A η).measurableSet

def transcriptEvent (n : ℕ) {H : Type*} (I : ℕ → Submodule ℝ E)
    (A : Submodule ℝ E) (η : ℝ) : Set (ActionHistory E (actionCount n) H) :=
  roundQueryTrace E n ⁻¹' prefixEvent I A η

theorem measurableSet_transcriptEvent (n : ℕ) {H : Type*} [MeasurableSpace H]
    (I : ℕ → Submodule ℝ E) (A : Submodule ℝ E) (η : ℝ) :
    MeasurableSet (transcriptEvent n (H := H) I A η) :=
  (roundQueryTrace_measurable n) (measurableSet_prefixEvent I A η)

end MatchingBounds1005.ScheduledPrefix
