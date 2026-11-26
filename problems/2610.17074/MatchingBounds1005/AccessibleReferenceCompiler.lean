import MatchingBounds1005.ScheduledContainment

/-!
# Compiling accessible reference state machines to the actual Haar protocol

The internal state can contain the algorithm seed and all private Gaussian
noise. Its updates receive only disclosed physical columns and physical
matrix responses. Latent inverse-query answers are discarded. The compiler
has exact source semantics, so no accessibility or posterior law is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.AccessibleReferenceCompiler
open ScheduledHaar

universe u
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {S : Type u} [MeasurableSpace S]

structure Update (S : Type u) [MeasurableSpace S] where
  next : S × E → S
  measurable_next : Measurable next

def Machine : List SourceKind → Type u
  | [] => PUnit
  | .disclose :: w => (E × Update (E := E) S) × Machine w
  | .query :: w => (PhysicalRequest (E := E) S × Update (E := E) S) × Machine w
  | .candidate :: w => (PhysicalRequest (E := E) S × Update (E := E) S) × Machine w

def run : (w : List SourceKind) → Machine (E := E) (S := S) w →
    (E →L[ℝ] E) → (E →L[ℝ] E) → S → S
  | [], _, _, _, s => s
  | .disclose :: w, M, Q, U, s => run w M.2 Q U (M.1.2.next (s, U M.1.1))
  | .query :: w, M, Q, U, s =>
      run w M.2 Q U (M.1.2.next (s, U (Q (U.adjoint (M.1.1.point s)))))
  | .candidate :: w, M, Q, U, s => run w M.2 Q U (M.1.2.next (s, M.1.1.point s))

def compile : (w : List SourceKind) → Machine (E := E) (S := S) w →
    {H : Type u} → [MeasurableSpace H] → (view : H → S) → Measurable view → SourcePolicy (E := E) w H
  | [], _, _, _, _, _ => PUnit.unit
  | .disclose :: w, M, _, _, view, hv =>
      (M.1.1, compile w M.2 (fun h => M.1.2.next (view h.1, h.2))
        (M.1.2.measurable_next.comp ((hv.comp measurable_fst).prodMk measurable_snd)))
  | .query :: w, M, _, _, view, hv =>
      (⟨fun h => M.1.1.point (view h), M.1.1.measurable_point.comp hv⟩,
        compile w M.2 (fun h => M.1.2.next (view h.1.1, h.2))
          (M.1.2.measurable_next.comp ((hv.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)))
  | .candidate :: w, M, _, _, view, hv =>
      (⟨fun h => M.1.1.point (view h), M.1.1.measurable_point.comp hv⟩,
        compile w M.2 (fun h => M.1.2.next (view h.1, h.2))
          (M.1.2.measurable_next.comp ((hv.comp measurable_fst).prodMk measurable_snd)))

def decode : (w : List SourceKind) → Machine (E := E) (S := S) w →
    {H : Type u} → [MeasurableSpace H] → (H → S) → SourceHistory E w H → S
  | [], _, _, _, view => view
  | .disclose :: w, M, _, _, view => decode w M.2 (fun h => M.1.2.next (view h.1, h.2))
  | .query :: w, M, _, _, view => decode w M.2 (fun h => M.1.2.next (view h.1.1, h.2))
  | .candidate :: w, M, _, _, view => decode w M.2 (fun h => M.1.2.next (view h.1, h.2))

theorem decode_measurable (w : List SourceKind) (M : Machine (E := E) (S := S) w)
    {H : Type u} [MeasurableSpace H] (view : H → S) (hv : Measurable view) :
    Measurable (decode w M view) := by
  induction w generalizing H with
  | nil => exact hv
  | cons kind w ih =>
      cases kind with
      | disclose => exact ih M.2 _ (M.1.2.measurable_next.comp ((hv.comp measurable_fst).prodMk measurable_snd))
      | query => exact ih M.2 _ (M.1.2.measurable_next.comp ((hv.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd))
      | candidate => exact ih M.2 _ (M.1.2.measurable_next.comp ((hv.comp measurable_fst).prodMk measurable_snd))

/-- Exact source-policy realization of the reference state machine. In a
query branch the inverse answer is present only in the analyst's source
history; the next policy view uses the physical matrix response alone. -/
theorem compile_correct (w : List SourceKind) (M : Machine (E := E) (S := S) w)
    {H : Type u} [MeasurableSpace H] (view : H → S) (hv : Measurable view)
    (Q U : E →L[ℝ] E) (h : H) :
    decode w M view ((compile w M view hv).run w Q U h) = run w M Q U (view h) := by
  induction w generalizing H with
  | nil => rfl
  | cons kind w ih =>
      cases kind <;>
        simp only [compile, SourcePolicy.run, decode, run] <;>
        apply ih

end MatchingBounds1005.AccessibleReferenceCompiler
