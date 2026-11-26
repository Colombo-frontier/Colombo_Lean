import Bilevel.CachedOuterProcedure
import Bilevel.CachedAnchorCertificate

/-! Measurable first-failure predicates and deterministic update certificates
for the executed cached outer kernel. Invalid initial dummy cache is ignored
only at iteration zero, where the algorithm unconditionally refreshes. -/
noncomputable section
open MeasureTheory
namespace Bilevel.CachedOuterProcedure

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

def traceBad (Λ cap e : ℝ) (x₀ : X) (n : ℕ) : Set (State X Y) :=
  {s | ∃ i < n, e < ‖s.1 i - gradient (P.hyperobjective P.canonicalResponse) (current Λ cap x₀ i s)‖}

def bad (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) : Set (State X Y) :=
  {s | s ∈ traceBad P Λ cap e x₀ n ∨
    (n ≠ 0 ∧ ¬ CachedAnchorProcedure.Certificate P s.2.1 rA η s.2.2)}

def middleBad (Λ cap radius e rA η : ℝ) (x₀ : X) (n : ℕ) : Set (State X Y) :=
  {s | s ∈ traceBad P Λ cap e x₀ n ∨
    ¬ CachedAnchorProcedure.Certificate P s.2.1 rA η s.2.2 ∨
    radius < ‖current Λ cap x₀ n s-s.2.1‖}

theorem initial_not_bad (Λ cap e rA η : ℝ) (x₀ : X) :
    initialState (Y := Y) x₀ ∉ bad P Λ cap e rA η x₀ 0 := by
  simp [bad, traceBad]

theorem traceBad_put (Λ cap e : ℝ) (x₀ : X) (n : ℕ) (s : State X Y) (v : X) :
    (put s.1 n v,s.2) ∈ traceBad P Λ cap e x₀ (n+1) ↔
      s ∈ traceBad P Λ cap e x₀ n ∨
        e < ‖v-gradient (P.hyperobjective P.canonicalResponse) (current Λ cap x₀ n s)‖ := by
  constructor
  · rintro ⟨i,hi,he⟩
    by_cases hin : i = n
    · subst i
      right
      simpa only [current, run_put_prefix Λ cap x₀ s.1 n v n (le_refl n), put, ite_true] using he
    · left
      refine ⟨i,by omega,?_⟩
      simpa only [current, run_put_prefix Λ cap x₀ s.1 n v i (by omega), put, if_neg hin] using he
  · rintro (⟨i,hi,he⟩ | he)
    · refine ⟨i,by omega,?_⟩
      simpa only [current, run_put_prefix Λ cap x₀ s.1 n v i (by omega), put,
        if_neg (by omega : i ≠ n)] using he
    · refine ⟨n,by omega,?_⟩
      simpa only [current, run_put_prefix Λ cap x₀ s.1 n v n (le_refl n), put, ite_true] using he

theorem bad_put_subset (Λ cap radius e rA η : ℝ) (x₀ : X) (n : ℕ) (s : State X Y)
    (hs : s ∉ middleBad P Λ cap radius e rA η x₀ n) (v : X)
    (hb : (put s.1 n v,s.2) ∈ bad P Λ cap e rA η x₀ (n+1)) :
    e < ‖v-gradient (P.hyperobjective P.canonicalResponse) (current Λ cap x₀ n s)‖ := by
  have hs' : s ∉ traceBad P Λ cap e x₀ n ∧
      CachedAnchorProcedure.Certificate P s.2.1 rA η s.2.2 ∧
      ‖current Λ cap x₀ n s-s.2.1‖ ≤ radius := by
    simpa only [middleBad, Set.mem_setOf_eq, not_or, not_not, not_lt] using hs
  rcases hb with hb | hb
  · exact (traceBad_put P Λ cap e x₀ n s v).mp hb |>.resolve_left hs'.1
  · exact False.elim (hb.2 hs'.2.1)

theorem middle_good_cache_error (Λ cap radius e rA η : ℝ) (x₀ : X) (yinit : Y)
    (n : ℕ) (s : State X Y) (hs : s ∉ middleBad P Λ cap radius e rA η x₀ n) :
    let p := estimatorInput Cf Λ cap x₀ yinit n s
    ‖p.2.1-P.fx p.1 (P.canonicalResponse.y p.1)‖ + Lg/μ *
      ‖p.2.2.1-P.fy p.1 (P.canonicalResponse.y p.1)‖ ≤
        (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius) := by
  have hs' : s ∉ traceBad P Λ cap e x₀ n ∧
      CachedAnchorProcedure.Certificate P s.2.1 rA η s.2.2 ∧
      ‖current Λ cap x₀ n s-s.2.1‖ ≤ radius := by
    simpa only [middleBad, Set.mem_setOf_eq, not_or, not_not, not_lt] using hs
  exact CachedAnchorProcedure.certificate_cached_error P _ _ rA η radius s.2.2 hs'.2.1
    (by simpa only [norm_sub_rev] using hs'.2.2)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

omit [BorelSpace Y] [SecondCountableTopology Y] in
theorem traceBad_measurable (Λ cap e : ℝ) (x₀ : X) (n : ℕ) :
    MeasurableSet (traceBad P Λ cap e x₀ n) := by
  unfold traceBad
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i < n
  · simp only [hi, true_and]
    exact measurableSet_lt measurable_const
      (((measurable_pi_apply i).comp measurable_fst).sub
        ((P.gradient_hyperobjective_lipschitz P.canonicalResponse).continuous.measurable.comp
          (current_measurable Λ cap x₀ i))).norm
  · simp [hi]

theorem bad_measurable (Λ cap e rA η : ℝ) (x₀ : X) (n : ℕ) :
    MeasurableSet (bad P Λ cap e rA η x₀ n) := by
  unfold bad
  apply (traceBad_measurable P Λ cap e x₀ n).union
  by_cases hn : n = 0
  · simp only [hn, ne_eq, not_true_eq_false, false_and]
    exact MeasurableSet.empty
  · simp only [hn, ne_eq, not_false_eq_true, true_and]
    exact ((CachedAnchorProcedure.certificate_joint_measurable P rA η).preimage measurable_snd).compl

theorem middleBad_measurable (Λ cap radius e rA η : ℝ) (x₀ : X) (n : ℕ) :
    MeasurableSet (middleBad P Λ cap radius e rA η x₀ n) := by
  apply (traceBad_measurable P Λ cap e x₀ n).union
  apply ((CachedAnchorProcedure.certificate_joint_measurable P rA η).preimage measurable_snd).compl.union
  exact measurableSet_lt measurable_const
    (((current_measurable Λ cap x₀ n).sub (measurable_fst.comp measurable_snd)).norm)

end Bilevel.CachedOuterProcedure
