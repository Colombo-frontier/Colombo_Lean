import SecondOrder.OjaStep
import SecondOrder.ContinuousBatch

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- Oja iterations driven by a fresh scalar-loss sample at each step. -/
def ojaHvpRun {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → Point d
  | 0, _ => v
  | N + 1, w => ojaStep η (sampledShiftedHessian P f x w.2)
      (ojaHvpRun P f η x v N w.1)

/-- The next query is formed from the old draws only. -/
def ojaHvpQuery {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) : HvpQuery d :=
  .hvp x (ojaHvpRun P f η x v N w)

theorem ojaHvpRun_succ_from_reply {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) (z : Ω) :
    ojaHvpRun P f η x v (N+1) (w,z) =
      ojaStepFromHvp P η (ojaHvpRun P f η x v N w)
        (hvpReply f z (ojaHvpQuery P f η x v N w)) := rfl

/-- An explicit ordered list of the samples and their single-point queries. -/
def ojaHvpTrace {Ω : Type*} {d : ℕ} (P : Parameters) (f : Ω → Point d → ℝ)
    (η : ℝ) (x v : Point d) : (N : ℕ) → Draws Ω N → List (Ω × HvpQuery d)
  | 0, _ => []
  | N+1, w => ojaHvpTrace P f η x v N w.1 ++ [(w.2,ojaHvpQuery P f η x v N w.1)]

theorem ojaHvpTrace_length {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) :
    (ojaHvpTrace P f η x v N w).length = N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [ojaHvpTrace, List.length_append, List.length_singleton, ih]

/-- Replaying the actual oracle replies produces exactly the same iterate. -/
theorem ojaHvpRun_eq_reply_fold {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) :
    (ojaHvpTrace P f η x v N w).foldl
      (fun u q => ojaStepFromHvp P η u (hvpReply f q.1 q.2)) v =
        ojaHvpRun P f η x v N w := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [ojaHvpTrace, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rfl

theorem ojaHvpTrace_queryPoint {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (N : ℕ) (w : Draws Ω N) :
    ∀ q ∈ ojaHvpTrace P f η x v N w, queryPoint q.2 = x := by
  induction N with
  | zero => simp [ojaHvpTrace]
  | succ N ih =>
    intro q hq
    simp only [ojaHvpTrace, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact ih w.1 q hq
    · rfl

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaHvpRun_measurable (h : CommonLoss μ P ν F f) (η : ℝ) (N : ℕ) :
    Measurable (fun w : (Point d × Point d) × Draws Ω N =>
      ojaHvpRun P f η w.1.1 w.1.2 N w.2) := by
  induction N with
  | zero => exact measurable_fst.snd
  | succ N ih =>
    have hp : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        (w.1, w.2.1)) := measurable_fst.prodMk measurable_snd.fst
    have hx : Measurable (fun w : (Point d × Point d) × Draws Ω N => w.1.1) :=
      measurable_fst.fst
    have hg : Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
        ((w.1, w.2.1), w.2.2)) := hp.prodMk measurable_snd.snd
    have hd := (h.shifted_hvp_adaptive_measurable hx ih).comp hg
    have hu := ih.comp hp
    change Measurable (fun w : (Point d × Point d) × (Draws Ω N × Ω) =>
      normalizeProbe (ojaHvpRun P f η w.1.1 w.1.2 N w.2.1 +
        η • sampledShiftedHessian P f w.1.1 w.2.2
          (ojaHvpRun P f η w.1.1 w.1.2 N w.2.1)))
    exact (normalizeProbe_measurable (d := d)).comp (hu.add (hd.const_smul η))

/-- Every finite iterate is a unit vector almost surely when initialized
with a unit vector; the event is uniform in the point and initialization. -/
theorem CommonLoss.ojaHvpRun_ae_norm (h : CommonLoss μ P ν F f)
    {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    ∀ᵐ w ∂drawsLaw μ N, ∀ (x v : Point d), ‖v‖ = 1 →
      ‖ojaHvpRun P f η x v N w‖ = 1 := by
  induction N with
  | zero => exact Eventually.of_forall (fun _ _ _ hv => hv)
  | succ N ih =>
    have hp := (Measure.quasiMeasurePreserving_fst (μ := drawsLaw μ N) (ν := μ)).ae ih
    have hz := (Measure.quasiMeasurePreserving_snd (μ := drawsLaw μ N) (ν := μ)).ae
      h.shifted_hessian_good
    filter_upwards [hp, hz] with w hw hz
    intro x v hv
    apply ojaStep_norm hη ((hz x).2.2 _).1
    have hu := hw x v hv
    exact norm_ne_zero_iff.mp (by rw [hu]; norm_num)

end
end SecondOrder
