import HeavyTail.Erasure
import Mathlib.MeasureTheory.Measure.Real

/-!
# Adaptive erasure transcripts with an arbitrary random seed

The policy queries a measurable function of its seed and the replies already
received. Unqueried transcript coordinates are zero padded. Fresh masks have
the finite independent product law, independent of the unrestricted seed law.
The zero-transcript coupling is proved recursively for the actual execution.
-/

open MeasureTheory
open scoped ENNReal

namespace HeavyTail

structure AdaptivePolicy (S X R Y : Type*) [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace R] [MeasurableSpace Y] (T : ℕ) where
  query : Fin T → S × (Fin T → R) → X
  query_measurable : ∀ i, Measurable (query i)
  output : S × (Fin T → R) → Y
  output_measurable : Measurable output

namespace AdaptivePolicy

variable {S X R Y : Type*} [MeasurableSpace S] [MeasurableSpace X]
  [MeasurableSpace R] [MeasurableSpace Y] [Zero R] {T : ℕ}

/-- Run the first `n` calls. At and after `T` calls the transcript is unchanged. -/
noncomputable def transcript (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R) (hypothesis : Bool)
    (seed : S) (masks : Fin T → Bool) : ℕ → (Fin T → R)
  | 0 => fun _ ↦ 0
  | n + 1 =>
    if hn : n < T then
      Function.update (transcript A oracle hypothesis seed masks n) ⟨n, hn⟩
        (oracle hypothesis
          (A.query ⟨n, hn⟩ (seed, transcript A oracle hypothesis seed masks n))
          (masks ⟨n, hn⟩))
    else transcript A oracle hypothesis seed masks n

noncomputable def execute (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R) (hypothesis : Bool)
    (ω : S × (Fin T → Bool)) : Y :=
  A.output (ω.1, A.transcript oracle hypothesis ω.1 ω.2 T)

/-- Future reply coordinates remain zero: queries cannot inspect future samples. -/
theorem transcript_future_zero (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R) (hypothesis : Bool)
    (seed : S) (masks : Fin T → Bool) (n : ℕ) (i : Fin T) (hi : n ≤ i.val) :
    A.transcript oracle hypothesis seed masks n i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [transcript]
    split_ifs with hn
    · have hneq : i ≠ (⟨n, hn⟩ : Fin T) := by
        intro heq
        have := congrArg Fin.val heq
        simp only [Fin.val_mk] at this
        omega
      rw [Function.update_of_ne hneq]
      exact ih (by omega)
    · exact ih (by omega)

/-- The first `n` replies depend only on the first `n` masks. -/
theorem transcript_prefix_invariance (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R) (hypothesis : Bool) (seed : S)
    (n : ℕ) (masks masks' : Fin T → Bool)
    (hprefix : ∀ i : Fin T, i.val < n → masks i = masks' i) :
    A.transcript oracle hypothesis seed masks n =
      A.transcript oracle hypothesis seed masks' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (fun i hi ↦ hprefix i (by omega))
    rw [transcript, transcript]
    split_ifs with hn
    · rw [hprev, hprefix ⟨n, hn⟩ (by simp)]
    · exact hprev

/-- The all-erased history is derived from execution, even with adaptive queries. -/
theorem transcript_all_erased (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R)
    (horacle : ∀ hypothesis x, oracle hypothesis x true = 0)
    (hypothesis : Bool) (seed : S) (masks : Fin T → Bool)
    (hmasks : ∀ i, masks i = true) (n : ℕ) :
    A.transcript oracle hypothesis seed masks n = fun _ ↦ 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [transcript]
    split_ifs with hn
    · rw [ih, hmasks, horacle]
      ext i
      by_cases hi : i = (⟨n, hn⟩ : Fin T) <;> simp [hi]
    · exact ih

theorem execute_all_erased (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R)
    (horacle : ∀ hypothesis x, oracle hypothesis x true = 0)
    (hypothesis : Bool) (ω : S × (Fin T → Bool))
    (hmasks : ∀ i, ω.2 i = true) :
    A.execute oracle hypothesis ω = A.output (ω.1, fun _ ↦ 0) := by
  unfold execute
  rw [A.transcript_all_erased oracle horacle hypothesis ω.1 ω.2 hmasks T]

theorem hypothesis_noninterference (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R)
    (horacle : ∀ hypothesis x, oracle hypothesis x true = 0)
    (ω : S × (Fin T → Bool)) (hmasks : ∀ i, ω.2 i = true) :
    A.execute oracle false ω = A.execute oracle true ω := by
  rw [A.execute_all_erased oracle horacle false ω hmasks,
    A.execute_all_erased oracle horacle true ω hmasks]

theorem transcript_measurable (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R)
    (horacle : ∀ h, Measurable (fun z : X × Bool ↦ oracle h z.1 z.2))
    (hypothesis : Bool) (n : ℕ) :
    Measurable (fun ω : S × (Fin T → Bool) ↦
      A.transcript oracle hypothesis ω.1 ω.2 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases hn : n < T
    · have hquery : Measurable (fun ω : S × (Fin T → Bool) ↦
          A.query ⟨n, hn⟩ (ω.1, A.transcript oracle hypothesis ω.1 ω.2 n)) :=
        (A.query_measurable ⟨n, hn⟩).comp (measurable_fst.prodMk ih)
      have hmask : Measurable (fun ω : S × (Fin T → Bool) ↦ ω.2 ⟨n, hn⟩) :=
        (measurable_pi_apply (⟨n, hn⟩ : Fin T)).comp measurable_snd
      have hreply := (horacle hypothesis).comp (hquery.prodMk hmask)
      apply measurable_pi_iff.mpr
      intro i
      by_cases hi : i = (⟨n, hn⟩ : Fin T)
      · subst i
        simpa only [transcript, dif_pos hn, Function.update_self] using hreply
      · simpa only [transcript, dif_pos hn, Function.update_of_ne hi] using
          (measurable_pi_apply i).comp ih
    · simpa only [transcript, dif_neg hn] using ih

theorem execute_measurable (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R)
    (horacle : ∀ h, Measurable (fun z : X × Bool ↦ oracle h z.1 z.2))
    (hypothesis : Bool) : Measurable (A.execute oracle hypothesis) :=
  A.output_measurable.comp
    (measurable_fst.prodMk (A.transcript_measurable oracle horacle hypothesis T))

end AdaptivePolicy

instance erasureSequenceLaw_isProbabilityMeasure (u : ℝ) (hu : u ≤ 1) (T : ℕ) :
    IsProbabilityMeasure (erasureSequenceLaw u hu T) := by
  unfold erasureSequenceLaw
  infer_instance

/-- The scalar importance-weighted erasure oracle at the actual chosen query. -/
noncomputable def adaptiveErasureOracle {X : Type*}
    (u : ℝ) (mean : Bool → X → ℝ) : Bool → X → Bool → ℝ :=
  fun h x b ↦ erasureReply u (mean h x) b

theorem adaptiveErasureOracle_zero {X : Type*} (u : ℝ) (mean : Bool → X → ℝ)
    (h : Bool) (x : X) : adaptiveErasureOracle u mean h x true = 0 := by
  simp [adaptiveErasureOracle, erasureReply]

theorem adaptiveErasureOracle_measurable {X : Type*} [MeasurableSpace X]
    (u : ℝ) (mean : Bool → X → ℝ) (hmean : ∀ h, Measurable (mean h)) (h : Bool) :
    Measurable (fun z : X × Bool ↦ adaptiveErasureOracle u mean h z.1 z.2) := by
  unfold adaptiveErasureOracle erasureReply
  exact Measurable.ite (measurable_snd (MeasurableSet.singleton true)) measurable_const
    (((hmean h).comp measurable_fst).div_const (1 - u))

/-- Unbiasedness holds at every selected query, including an adaptive query. -/
theorem adaptiveErasureOracle_unbiased {X : Type*} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (mean : Bool → X → ℝ) (h : Bool) (x : X) :
    (∫ b, adaptiveErasureOracle u mean h x b ∂(erasureCoin u hu1.le).toMeasure) =
      mean h x := erasure_unbiased hu0 hu1 (mean h x)

/-- Exact local centered moment for the query-dependent oracle kernel. -/
theorem adaptiveErasureOracle_centered_moment {X : Type*} {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) (mean : Bool → X → ℝ)
    (h : Bool) (x : X) (p : ℝ) :
    (∫ b, |adaptiveErasureOracle u mean h x b - mean h x| ^ p
      ∂(erasureCoin u hu1.le).toMeasure) =
      |mean h x| ^ p * (u + u ^ p / (1 - u) ^ (p - 1)) :=
  erasure_centered_moment hu0 hu1 (mean h x) p

/-- The seed law is unrestricted; this is not a finite-seed abstraction. -/
theorem measurable_binary_testing_half {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P] (decode : S → Bool) (hd : Measurable decode) :
    ∃ h : Bool, (1 / 2 : ℝ) ≤ P.real {s | decode s ≠ h} := by
  let B : Set S := {s | decode s ≠ false}
  have hB : MeasurableSet B := (hd (MeasurableSet.singleton false)).compl
  have hBc : Bᶜ = {s | decode s ≠ true} := by
    ext s
    cases hs : decode s <;> simp [B, hs]
  have hsum := measureReal_add_measureReal_compl (μ := P) hB
  rw [hBc, measureReal_univ_eq_one] at hsum
  by_cases hhalf : (1 / 2 : ℝ) ≤ P.real B
  · exact ⟨false, hhalf⟩
  · exact ⟨true, by linarith⟩

/--
For every measurable adaptive policy and arbitrary seed law, one hidden
hypothesis has testing error at least `u^T/2`. The conclusion concerns the
actual executed output, not an assumed identical transcript.
-/
theorem adaptive_erasure_testing_lower
    {S X R Y : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace R] [MeasurableSpace Y] [Zero R] {T : ℕ}
    (A : AdaptivePolicy S X R Y T)
    (oracle : Bool → X → Bool → R)
    (horacle0 : ∀ hypothesis x, oracle hypothesis x true = 0)
    (horacleMeas : ∀ h, Measurable (fun z : X × Bool ↦ oracle h z.1 z.2))
    (P : Measure S) [IsProbabilityMeasure P]
    (decode : Y → Bool) (hdecode : Measurable decode)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ h : Bool,
      MeasurableSet {ω | decode (A.execute oracle h ω) ≠ h} ∧
      u ^ T / 2 ≤ (P.prod (erasureSequenceLaw u hu1 T)).real
        {ω | decode (A.execute oracle h ω) ≠ h} := by
  let d : S → Bool := fun s ↦ decode (A.output (s, fun _ ↦ 0))
  have hd : Measurable d :=
    hdecode.comp (A.output_measurable.comp (measurable_id.prodMk measurable_const))
  obtain ⟨h, hh⟩ := measurable_binary_testing_half P d hd
  refine ⟨h, ?_, ?_⟩
  · exact ((hdecode.comp (A.execute_measurable oracle horacleMeas h))
      (MeasurableSet.singleton h)).compl
  let B : Set (Fin T → Bool) := {b | ∀ i, b i = true}
  let E : Set S := {s | d s ≠ h}
  have hsubset : E ×ˢ B ⊆ {ω | decode (A.execute oracle h ω) ≠ h} := by
    intro ω hω
    change decode (A.execute oracle h ω) ≠ h
    rw [A.execute_all_erased oracle horacle0 h ω hω.2]
    exact hω.1
  have hmass : (P.prod (erasureSequenceLaw u hu1 T)).real (E ×ˢ B) =
      P.real E * u ^ T := by
    rw [measureReal_prod_prod]
    change P.real E * (erasureSequenceLaw u hu1 T B).toReal = _
    rw [all_erased_probability_real hu0 hu1]
  calc
    u ^ T / 2 ≤ P.real E * u ^ T := by
      have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hu0 T)
      dsimp [E]
      linarith
    _ = (P.prod (erasureSequenceLaw u hu1 T)).real (E ×ˢ B) := hmass.symm
    _ ≤ _ := measureReal_mono hsubset

/-- Specialization to the actual unbiased scalar erasure oracle. -/
theorem adaptive_scalar_erasure_testing_lower
    {S X Y : Type*} [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]
    {T : ℕ} (A : AdaptivePolicy S X ℝ Y T)
    (mean : Bool → X → ℝ) (hmean : ∀ h, Measurable (mean h))
    (P : Measure S) [IsProbabilityMeasure P]
    (decode : Y → Bool) (hdecode : Measurable decode)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∃ h : Bool,
      MeasurableSet {ω | decode (A.execute (adaptiveErasureOracle u mean) h ω) ≠ h} ∧
      u ^ T / 2 ≤ (P.prod (erasureSequenceLaw u hu1 T)).real
        {ω | decode (A.execute (adaptiveErasureOracle u mean) h ω) ≠ h} :=
  adaptive_erasure_testing_lower A (adaptiveErasureOracle u mean)
    (adaptiveErasureOracle_zero u mean) (adaptiveErasureOracle_measurable u mean hmean)
    P decode hdecode hu0 hu1

end HeavyTail
