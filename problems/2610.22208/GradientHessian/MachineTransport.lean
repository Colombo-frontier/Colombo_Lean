import GradientHessian.Machine

/-! Exact measurable transport of arbitrary mixed-query machines. Reply
decoders may use the original query point, as needed for public padding.
Internal computation, seed/state spaces, and unqueried outputs are unrestricted. -/

namespace GradientHessian.Machine
open MeasureTheory Set

variable {Seed State X Y Z X' Y' Z' : Type*}
  [MeasurableSpace Seed] [MeasurableSpace State]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']

def Policy.transport (P : Policy Seed State X Y Z)
    (q : X → X') (o : X × Y' → Y) (r : X × Z' → Z)
    (hq : Measurable q) (ho : Measurable o) (hr : Measurable r) : Policy Seed State X' Y' Z' where
  initial := P.initial
  mode := P.mode
  point := q ∘ P.point
  output := q ∘ P.output
  think := P.think
  ordinaryNext := fun sy => P.ordinaryNext (sy.1, o (P.point sy.1, sy.2))
  richNext := fun sy => P.richNext (sy.1, r (P.point sy.1, sy.2))
  initial_measurable := P.initial_measurable
  mode_measurable := P.mode_measurable
  point_measurable := hq.comp P.point_measurable
  output_measurable := hq.comp P.output_measurable
  think_measurable := P.think_measurable
  ordinaryNext_measurable := P.ordinaryNext_measurable.comp
    (measurable_fst.prodMk (ho.comp ((P.point_measurable.comp measurable_fst).prodMk measurable_snd)))
  richNext_measurable := P.richNext_measurable.comp
    (measurable_fst.prodMk (hr.comp ((P.point_measurable.comp measurable_fst).prodMk measurable_snd)))

variable (P : Policy Seed State X Y Z) (q : X → X') (o : X × Y' → Y) (r : X × Z' → Z)
    (hq : Measurable q) (ho : Measurable o) (hr : Measurable r)
    (ordinary : X → Y) (rich : X → Z) (ordinary' : X' → Y') (rich' : X' → Z')
    (hordinary : ∀ x, o (x, ordinary' (q x)) = ordinary x)
    (hrich : ∀ x, r (x, rich' (q x)) = rich x)

include hordinary hrich

theorem Policy.transport_step (s : State) :
    (P.transport q o r hq ho hr).step ordinary' rich' s = P.step ordinary rich s := by
  simp only [Policy.step, Policy.transport, Function.comp_apply, hordinary, hrich]

theorem Policy.transport_run (n : ℕ) (seed : Seed) :
    (P.transport q o r hq ho hr).run ordinary' rich' n seed = P.run ordinary rich n seed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Policy.run, ih]
    exact P.transport_step q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich _

theorem Policy.transport_output (n : ℕ) (seed : Seed) :
    (P.transport q o r hq ho hr).output ((P.transport q o r hq ho hr).run ordinary' rich' n seed) =
      q (P.output (P.run ordinary rich n seed)) := by
  rw [P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

theorem Policy.transport_ordinaryCount (n : ℕ) (seed : Seed) :
    (P.transport q o r hq ho hr).ordinaryCount ordinary' rich' n seed = P.ordinaryCount ordinary rich n seed := by
  simp only [Policy.ordinaryCount, P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

theorem Policy.transport_richCount (n : ℕ) (seed : Seed) :
    (P.transport q o r hq ho hr).richCount ordinary' rich' n seed = P.richCount ordinary rich n seed := by
  simp only [Policy.richCount, P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

theorem Policy.transport_hasCaps (G H : ℕ) :
    (P.transport q o r hq ho hr).HasCaps ordinary' rich' G H ↔ P.HasCaps ordinary rich G H := by
  simp only [Policy.HasCaps,
    P.transport_ordinaryCount q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich,
    P.transport_richCount q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]

theorem Policy.transport_terminates :
    (P.transport q o r hq ho hr).Terminates ordinary' rich' ↔ P.Terminates ordinary rich := by
  simp only [Policy.Terminates, P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

theorem Policy.transport_terminatesAlmostSurely (μ : Measure Seed) :
    (P.transport q o r hq ho hr).TerminatesAlmostSurely ordinary' rich' μ ↔
      P.TerminatesAlmostSurely ordinary rich μ := by
  simp only [Policy.TerminatesAlmostSurely, P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

theorem Policy.transport_successBy (good : Set X') (N : ℕ) :
    (P.transport q o r hq ho hr).successBy ordinary' rich' good N =
      P.successBy ordinary rich (q ⁻¹' good) N := by
  ext seed
  simp only [Policy.successBy, Set.mem_setOf_eq,
    P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

theorem Policy.transport_success (good : Set X') :
    (P.transport q o r hq ho hr).success ordinary' rich' good =
      P.success ordinary rich (q ⁻¹' good) := by
  ext seed
  simp only [Policy.success, Set.mem_setOf_eq,
    P.transport_run q o r hq ho hr ordinary rich ordinary' rich' hordinary hrich]
  rfl

end GradientHessian.Machine
