import SampleReuse.PaddingAdmissible
import SecondOrder.OracleAlgorithm

open SecondOrder MeasureTheory

namespace SampleReuse
noncomputable section

def liftRichReply {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d) (r : RichReply m) : RichReply d :=
  (r.1,U r.2.1,liftedHessian U r.2.2)

theorem liftRichReply_continuous {m d : ℕ} (U : Point m →ₗᵢ[ℝ] Point d) :
    Continuous (liftRichReply U) :=
  continuous_fst.prodMk ((U.continuous.comp continuous_snd.fst).prodMk
    ((liftedHessian U).continuous.comp continuous_snd.snd))

theorem richReply_padding {Ω : Type*} {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d) (F : Ω → Point m → ℝ)
    (hF : ∀ z, ContDiff ℝ 2 (F z)) (z : Ω) (x : Point d) :
    liftRichReply U (richReply F z (isometryProjection U x)) =
      richReply (fun z => paddedLoss U (F z)) z x := by
  simp only [richReply,liftRichReply,SecondOrder.hessian]
  rw [paddedLoss_hessian U (hF z),paddedLoss_gradient U ((hF z).differentiable (by norm_num))]
  rfl

/-- A fixed sample table is retained through the entire execution. -/
def persistentScalarRun {Ω H S : Type*} {d : ℕ}
    (P : QueryPolicy (Point d × H) (RichReply d) S)
    (F : Ω → Point d → ℝ) (table : H → Ω) : ℕ → S
  | 0 => P.initial
  | n+1 => let s := persistentScalarRun P F table n
    let q := P.query n s
    P.update n s (richReply F (table q.2) q.1)

/-- Simulate a larger-dimensional algorithm using the original oracle.
Every call keeps its handle, projects its point, and zero-pads the true reply. -/
def projectPersistentPolicy {H S : Type*} {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d)
    (P : QueryPolicy (Point d × H) (RichReply d) S) :
    QueryPolicy (Point m × H) (RichReply m) S where
  initial := P.initial
  query n s := (isometryProjection U (P.query n s).1,(P.query n s).2)
  update n s r := P.update n s (liftRichReply U r)

theorem projectPersistentPolicy_measurable {Ξ H S : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S] {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d)
    (P : Ξ → QueryPolicy (Point d × H) (RichReply d) S)
    (hP : MeasurableQueryPolicyFamily P) :
    MeasurableQueryPolicyFamily (fun ξ => projectPersistentPolicy U (P ξ)) := by
  refine ⟨hP.initial,?_,?_⟩
  · intro n
    exact (((isometryProjection U).continuous.measurable.comp (hP.query n).fst).prodMk (hP.query n).snd)
  · intro n
    exact (hP.update n).comp (measurable_fst.prodMk
      (measurable_snd.fst.prodMk ((liftRichReply_continuous U).measurable.comp measurable_snd.snd)))

theorem projectPersistentPolicy_run {Ω H S : Type*} {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d)
    (P : QueryPolicy (Point d × H) (RichReply d) S)
    (F : Ω → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (table : H → Ω) (n : ℕ) :
    persistentScalarRun (projectPersistentPolicy U P) F table n =
      persistentScalarRun P (fun z => paddedLoss U (F z)) table n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [persistentScalarRun]
    rw [ih]
    simp only [projectPersistentPolicy,richReply_padding U F hF]

def projectPersistentAlgorithm {H S : Type*} {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d)
    (P : OracleAlgorithm (Point d × H) (RichReply d) (Point d) S) :
    OracleAlgorithm (Point m × H) (RichReply m) (Point m) S where
  toQueryPolicy := projectPersistentPolicy U P.toQueryPolicy
  output n s := isometryProjection U (P.output n s)

theorem projectPersistentAlgorithm_measurable {Ξ H S : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace H] [MeasurableSpace S] {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d)
    (P : Ξ → OracleAlgorithm (Point d × H) (RichReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) :
    MeasurableOracleAlgorithmFamily (fun ξ => projectPersistentAlgorithm U (P ξ)) :=
  ⟨projectPersistentPolicy_measurable U _ hP.toMeasurableQueryPolicyFamily,
    fun n => (isometryProjection U).continuous.measurable.comp (hP.output n)⟩

/-- The simulated output is exactly the projected larger-dimensional output;
there are the same number of calls and the same persistent handles. -/
theorem projectPersistentAlgorithm_output {Ω H S : Type*} {m d : ℕ}
    (U : Point m →ₗᵢ[ℝ] Point d)
    (P : OracleAlgorithm (Point d × H) (RichReply d) (Point d) S)
    (F : Ω → Point m → ℝ) (hF : ∀ z, ContDiff ℝ 2 (F z)) (table : H → Ω) (n : ℕ) :
    (projectPersistentAlgorithm U P).output n
      (persistentScalarRun (projectPersistentAlgorithm U P).toQueryPolicy F table n) =
      isometryProjection U (P.output n (persistentScalarRun P.toQueryPolicy
        (fun z => paddedLoss U (F z)) table n)) := by
  change isometryProjection U (P.output n (persistentScalarRun (projectPersistentPolicy U P.toQueryPolicy)
    F table n)) = _
  rw [projectPersistentPolicy_run U P.toQueryPolicy F hF]

end
end SampleReuse
