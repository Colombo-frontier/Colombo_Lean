import Smoothness2601.AdaptiveModel
import Smoothness2601.DeferredTail

/-! Deterministic seeded executions of an arbitrary Adaptive.Algorithm and
the deferred-prefix simulation. Randomness in the initial memory and coins is
left outside the pathwise theorem; no span or query-norm restriction is placed
on the algorithm. -/
noncomputable section
namespace Smoothness2601.PrefixSimulator
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry
open scoped BigOperators

def truncate {d T : ℕ} (U : Frame d T) (k : ℕ) : Frame d T :=
  fun i => if i.val < k then U i else 0

theorem truncate_measurable (d T k : ℕ) : Measurable (truncate (d := d) (T := T) · k) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val < k
  · simpa only [truncate,if_pos hi] using (measurable_pi_apply i : Measurable (fun U : Frame d T => U i))
  · simp only [truncate,if_neg hi]
    exact measurable_const

theorem truncate_truncate {d T : ℕ} (U : Frame d T) {j k : ℕ} (hjk : j ≤ k) :
    truncate (truncate U k) j = truncate U j := by
  funext i
  by_cases hi : i.val < j
  · simp [truncate,hi,hi.trans_le hjk]
  · simp [truncate,hi]

theorem truncate_eq_of_le {d T : ℕ} {U V : Frame d T} {j k : ℕ} (hjk : j ≤ k)
    (he : truncate U k = truncate V k) : truncate U j = truncate V j := by
  rw [← truncate_truncate U hjk,← truncate_truncate V hjk,he]

def prefixCount (T : ℕ) (coins : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t+1 => min T (prefixCount T coins t+if coins t then 1 else 0)

theorem prefixCount_le (T : ℕ) (coins : ℕ → Bool) (t : ℕ) : prefixCount T coins t ≤ T := by
  cases t with
  | zero => simp [prefixCount]
  | succ t => exact min_le_left _ _

theorem prefixCount_mono (T : ℕ) (coins : ℕ → Bool) (t : ℕ) :
    prefixCount T coins t ≤ prefixCount T coins (t+1) := by
  rw [prefixCount]
  exact le_min (prefixCount_le T coins t) (Nat.le_add_right _ _)

section Algorithm
variable {d T : ℕ}
variable (A : Adaptive.Algorithm (Space d) ℝ)
variable (reply : Frame d T → Adaptive.Query (Space d) ℝ → Bool → Joint (Space d) ℝ)
variable (coins : ℕ → Bool)

def realState (initial : A.Memory) (U : Frame d T) : ℕ → A.Memory
  | 0 => initial
  | t+1 => A.update t (realState initial U t,reply U (A.query t (realState initial U t)) (coins t))

def simulatedState (initial : A.Memory) (U : Frame d T) : ℕ → A.Memory
  | 0 => initial
  | t+1 => A.update t (simulatedState initial U t,
      reply (truncate U (prefixCount T coins (t+1)))
        (A.query t (simulatedState initial U t)) (coins t))

/-- The entire simulator state before t is a function of the exposed prefix.
The algorithm can keep arbitrary private memory and choose arbitrary points. -/
theorem simulatedState_prefix (initial : A.Memory) (t : ℕ) (U V : Frame d T)
    (he : truncate U (prefixCount T coins t) = truncate V (prefixCount T coins t)) :
    simulatedState A reply coins initial U t = simulatedState A reply coins initial V t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp := ih (truncate_eq_of_le (prefixCount_mono T coins t) he)
    simp only [simulatedState,hp,he]

theorem simulatedState_measurable
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (t : ℕ) : Measurable (fun p : A.Memory × Frame d T => simulatedState A reply coins p.1 p.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    have ht : Measurable (fun p : A.Memory × Frame d T => truncate p.2 (prefixCount T coins (t+1))) :=
      (truncate_measurable d T (prefixCount T coins (t+1))).comp measurable_snd
    have hq := (A.query_measurable t).comp ih
    have hr' := hr.comp (ht.prodMk (hq.prodMk (measurable_const (a := coins t))))
    exact (A.update_measurable t).comp (ih.prodMk hr')

theorem realState_measurable
    (hr : Measurable (fun p : Frame d T × (Adaptive.Query (Space d) ℝ × Bool) => reply p.1 p.2.1 p.2.2))
    (t : ℕ) : Measurable (fun p : A.Memory × Frame d T => realState A reply coins p.1 p.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    have hq := (A.query_measurable t).comp ih
    have hr' := hr.comp (measurable_snd.prodMk (hq.prodMk (measurable_const (a := coins t))))
    exact (A.update_measurable t).comp (ih.prodMk hr')

/-- A local response identity couples the complete real and simulated
transcripts on the event checked along the simulated execution. -/
theorem states_coupled (Safe : Frame d T → ℕ → Adaptive.Query (Space d) ℝ → Prop)
    (hlocal : ∀ U k q c, Safe U k q →
      reply U q c = reply (truncate U (min T (k+if c then 1 else 0))) q c)
    (initial : A.Memory) (U : Frame d T) (N : ℕ)
    (hsafe : ∀ t < N, Safe U (prefixCount T coins t)
      (A.query t (simulatedState A reply coins initial U t))) :
    realState A reply coins initial U N = simulatedState A reply coins initial U N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hp := ih (fun t ht => hsafe t (Nat.lt_succ_of_lt ht))
    simp only [realState,simulatedState,hp]
    rw [hlocal U (prefixCount T coins N) _ (coins N) (hsafe N (Nat.lt_succ_self N))]
    rfl

theorem outputs_coupled (Safe : Frame d T → ℕ → Adaptive.Query (Space d) ℝ → Prop)
    (hlocal : ∀ U k q c, Safe U k q →
      reply U q c = reply (truncate U (min T (k+if c then 1 else 0))) q c)
    (initial : A.Memory) (U : Frame d T) (N : ℕ)
    (hsafe : ∀ t < N, Safe U (prefixCount T coins t)
      (A.query t (simulatedState A reply coins initial U t))) :
    A.output (realState A reply coins initial U N) = A.output (simulatedState A reply coins initial U N) :=
  congrArg A.output (states_coupled A reply coins Safe hlocal initial U N hsafe)

end Algorithm
end Smoothness2601.PrefixSimulator
