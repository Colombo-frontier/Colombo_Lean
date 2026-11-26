import SampleReuse.Model
import SecondOrder.OracleAlgorithm
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-! A persistent common-loss derivative oracle. Handles index an immutable
sample tape; a policy sees only its private seed and numerical replies.
The unrequested derivative is replaced by zero. This is a finite-handle,
finite-execution foundation for the upper algorithm, not its success proof. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

/-- `true` requests the gradient, `false` the complete Hessian. -/
abbrev PersistentQuery (H d : ℕ) := Bool × (Fin H × Point d)
abbrev PersistentReply (d : ℕ) := Point d × (Point d →L[ℝ] Point d)
abbrev SampleTape (H : ℕ) (Ω : Type*) := Fin H → Ω

def persistentReply {Ω : Type*} {H d : ℕ} (F : Ω → Point d → ℝ)
    (tape : SampleTape H Ω) (q : PersistentQuery H d) : PersistentReply d :=
  if q.1 then (gradient (F (tape q.2.1)) q.2.2, 0)
  else (0, hessian (F (tape q.2.1)) q.2.2)

@[simp] theorem persistentReply_gradient {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x : Point d) :
    persistentReply F tape (true, r, x) = (gradient (F (tape r)) x, 0) := rfl

@[simp] theorem persistentReply_hessian {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x : Point d) :
    persistentReply F tape (false, r, x) = (0, hessian (F (tape r)) x) := rfl

theorem persistentReply_same_sample_gradient {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x y : Point d) :
    (persistentReply F tape (true, r, x)).1 - (persistentReply F tape (true, r, y)).1 =
      gradient (F (tape r)) x - gradient (F (tape r)) y := rfl

theorem persistentReply_same_sample_hessian {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x y : Point d) :
    (persistentReply F tape (false, r, x)).2 - (persistentReply F tape (false, r, y)).2 =
      hessian (F (tape r)) x - hessian (F (tape r)) y := rfl

theorem persistentReply_tape_congr {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape tape' : SampleTape H Ω) (q : PersistentQuery H d)
    (h : tape q.2.1 = tape' q.2.1) : persistentReply F tape q = persistentReply F tape' q := by
  simp only [persistentReply, h]

theorem measurable_sample_lookup {Ω : Type*} [MeasurableSpace Ω] (H : ℕ) :
    Measurable (fun w : SampleTape H Ω × Fin H => w.1 w.2) :=
  measurable_from_prod_countable (fun r => measurable_pi_apply r)

theorem persistentReply_measurable {Ω : Type*} [MeasurableSpace Ω] {H d : ℕ}
    (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2)) :
    Measurable (fun w : SampleTape H Ω × PersistentQuery H d => persistentReply F w.1 w.2) := by
  have hz : Measurable (fun w : SampleTape H Ω × PersistentQuery H d => w.1 w.2.2.1) :=
    (measurable_sample_lookup H).comp (measurable_fst.prodMk measurable_snd.snd.fst)
  have hpoint : Measurable (fun w : SampleTape H Ω × PersistentQuery H d => w.2.2.2) :=
    measurable_snd.snd.snd
  have hgrad : Measurable (fun w : SampleTape H Ω × PersistentQuery H d =>
      (gradient (F (w.1 w.2.2.1)) w.2.2.2, (0 : Point d →L[ℝ] Point d))) :=
    (hg.comp (hz.prodMk hpoint)).prodMk measurable_const
  have hhess : Measurable (fun w : SampleTape H Ω × PersistentQuery H d =>
      ((0 : Point d), hessian (F (w.1 w.2.2.1)) w.2.2.2)) :=
    measurable_const.prodMk (hH.comp (hz.prodMk hpoint))
  exact Measurable.ite ((measurableSet_singleton true).preimage measurable_snd.fst) hgrad hhess

/-- A finite iid sample tape is sampled once, then retained for the run. -/
def sampleTapeLaw {Ω : Type*} [MeasurableSpace Ω] (H : ℕ) (μ : Measure Ω) :
    Measure (SampleTape H Ω) := Measure.pi (fun _ : Fin H => μ)

instance sampleTapeLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (H : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (sampleTapeLaw H μ) := by
  unfold sampleTapeLaw
  infer_instance

theorem sampleTapeLaw_marginal {Ω : Type*} [MeasurableSpace Ω]
    (H : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] (r : Fin H) :
    (sampleTapeLaw H μ).map (fun tape => tape r) = μ := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply r) hs]
  have he : (fun tape : SampleTape H Ω => tape r) ⁻¹' s =
      Set.pi Set.univ (Function.update (fun _ : Fin H => Set.univ) r s) := by
    ext tape
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h i
      by_cases hi : i = r
      · subst i; simpa using h
      · simp [Function.update_of_ne hi]
    · intro h
      simpa using h r
  rw [he, sampleTapeLaw, Measure.pi_pi]
  rw [Finset.prod_eq_single r]
  · simp
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · simp

theorem sampleTapeLaw_independent {Ω : Type*} [MeasurableSpace Ω]
    (H : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    iIndepFun (fun r (tape : SampleTape H Ω) => tape r) (sampleTapeLaw H μ) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun r => (measurable_pi_apply r).aemeasurable)]
  simp_rw [sampleTapeLaw_marginal]
  exact Measure.map_id

/-- Each call chooses a handle, point and derivative using only the current
policy state. The oracle's tape is never passed to a query or update map. -/
def persistentRun {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) : ℕ → S
  | 0 => P.initial
  | n + 1 => P.update n (persistentRun P F tape n)
      (persistentReply F tape (P.query n (persistentRun P F tape n)))

theorem persistentRun_measurable {Ω S Ξ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace Ξ] {H d : ℕ}
    (P : Ξ → QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (hP : MeasurableQueryPolicyFamily P) (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2)) (n : ℕ) :
    Measurable (fun w : Ξ × SampleTape H Ω => persistentRun (P w.1) F w.2 n) := by
  induction n with
  | zero => exact hP.initial.comp measurable_fst
  | succ n ih =>
    have hq := (hP.query n).comp (measurable_fst.prodMk ih)
    have hr := (persistentReply_measurable F hg hH).comp (measurable_snd.prodMk hq)
    exact (hP.update n).comp (measurable_fst.prodMk (ih.prodMk hr))

/-- Changing unseen samples cannot alter the executed state. Agreement is
required only on handles actually queried along the first execution. -/
theorem persistentRun_tape_congr {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape tape' : SampleTape H Ω) (n : ℕ)
    (h : ∀ k < n, tape (P.query k (persistentRun P F tape k)).2.1 =
      tape' (P.query k (persistentRun P F tape k)).2.1) :
    persistentRun P F tape n = persistentRun P F tape' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := ih (fun k hk => h k (by omega))
    have hr := persistentReply_tape_congr F tape tape' (P.query n (persistentRun P F tape n))
      (h n (by omega))
    simp only [persistentRun]
    rw [← hs, hr]

theorem persistentRun_unchanged_by_unqueried_handle {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (n : ℕ) (r : Fin H) (z : Ω)
    (h : ∀ k < n, (P.query k (persistentRun P F tape k)).2.1 ≠ r) :
    persistentRun P F tape n = persistentRun P F (Function.update tape r z) n := by
  apply persistentRun_tape_congr
  intro k hk
  exact (Function.update_of_ne (h k hk) z tape).symm

def gradientCallCount {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, if (P.query k (persistentRun P F tape k)).1 then 1 else 0

def hessianCallCount {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, if (P.query k (persistentRun P F tape k)).1 then 0 else 1

theorem derivative_call_counts {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (n : ℕ) :
    gradientCallCount P F tape n + hessianCallCount P F tape n = n := by
  unfold gradientCallCount hessianCallCount
  rw [← Finset.sum_add_distrib]
  have he (k : ℕ) : (if (P.query k (persistentRun P F tape k)).1 then 1 else 0) +
      (if (P.query k (persistentRun P F tape k)).1 then 0 else 1) = (1 : ℕ) := by
    split_ifs <;> omega
  simp_rw [he]
  simp

end
end SampleReuse
