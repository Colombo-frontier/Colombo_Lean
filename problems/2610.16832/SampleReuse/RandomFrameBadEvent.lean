import SampleReuse.RandomFramePolicy
import SampleReuse.RandomFrameConcreteOracle
import SampleReuse.RandomFrameEmbedding

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory SecondOrder RandomizedFO2003 Rotations
open scoped InnerProductSpace

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def projectionBadEvent {m N : ℕ} (hN : N < m) (e : Fin m → E)
    (q : ∀ r : Fin (N+1), Ω × (Fin r.val → E) → E) (R t : ℝ) :
    Set (Ω × Rotation E) := {p | ∃ r : Fin (N+1), ∃ j : Fin m, r.val ≤ j.val ∧
      ‖q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k)))‖ ≤ R ∧
      t ≤ |⟪q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k))),
        isometry E p.2 (e j)⟫_ℝ|}

theorem projectionBadEvent_bound {m N : ℕ} (hN : N < m)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (e : Fin m → E) (he : Orthonormal ℝ e)
    (q : ∀ r : Fin (N+1), Ω × (Fin r.val → E) → E) (hq : ∀ r, Measurable (q r))
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    (μ.prod (haarLaw E)).real (projectionBadEvent hN e q R t) ≤
      ((m : ℝ) * (N+1)) *
        (2 * Real.exp (-((Module.finrank ℝ E - N : ℕ) : ℝ) * t ^ 2 / (2 * R ^ 2))) :=
  sequential_frame_tail hN μ e he q hq hR ht

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
theorem projection_lt_of_not_bad {m N : ℕ} (hN : N < m) (e : Fin m → E)
    (q : ∀ r : Fin (N+1), Ω × (Fin r.val → E) → E) (R t : ℝ)
    (p : Ω × Rotation E) (hgood : p ∉ projectionBadEvent hN e q R t)
    (r : Fin (N+1)) (j : Fin m) (hrj : r.val ≤ j.val)
    (hball : ‖q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k)))‖ ≤ R) :
    |⟪q r (p.1, fun k => isometry E p.2 (e (prefixIndex hN r k))),
      isometry E p.2 (e j)⟫_ℝ| < t := by
  by_contra h
  exact hgood ⟨r, j, hrj, hball, le_of_not_gt h⟩

def radialPolicyStages {d T : ℕ}
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (A β b R : ℝ) (N : ℕ)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d) :=
  policyStages query (fun n => prefixRadialReply (d := d) T n A β b R) N output

theorem measurable_radialPolicyStages {d T : ℕ}
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      query n p.1 p.2)) (A β b : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (ho : Measurable (fun p : Ω × (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      output p.1 p.2)) (r : Fin (N+1)) :
    Measurable (radialPolicyStages (T := T) query A β b R N output r) :=
  measurable_policyStages query _ hq
    (fun n => measurable_prefixRadialReply T n A β b hR) N output ho r

theorem rotated_columns_prefix {d T N : ℕ} (hN : N < T+1)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (V : Rotation (Point d)) (r : Fin (N+1)) :
    (fun k : Fin r.val => frameColumns (rotatedEmbedding U V) k.val) =
      (fun k => isometry (Point d) V (U (blockUnit (prefixIndex hN r k) (1:ℝ)))) := by
  funext k
  have hk : k.val < T+1 := by omega
  simp only [frameColumns, dif_pos hk, rotatedEmbedding_column]
  rfl

omit [MeasurableSpace Ω] in
theorem radialPolicyStages_query_identity {d T N : ℕ} (hN : N < T+1)
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (V : Rotation (Point d)) (A β b R : ℝ)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (ω : Ω) (r : Fin N) :
    radialPolicyStages (T := T) query A β b R N output r.castSucc
      (ω, fun k => isometry (Point d) V (U (blockUnit (prefixIndex hN r.castSucc k) (1:ℝ)))) =
    queryAt query (radialPrefixOracle (rotatedEmbedding U V) A β b R) ω () r.val := by
  change policyStages query _ N output r.castSucc _ = _
  rw [policyStages_query, radialPrefixOracle, queryAt_eq_prefixQuery]
  exact congrArg (fun z => prefixQuery query
    (fun n => prefixRadialReply (d := d) T n A β b R) r.val (ω,z))
      (rotated_columns_prefix hN U V r.castSucc).symm

omit [MeasurableSpace Ω] in
theorem radial_full_transcript_eq_on_good {d T N : ℕ} (hN : N < T+1)
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b : ℝ) {R t : ℝ}
    (hR : 0 < R) (hβ : 0 ≤ β) (hβt : β*t ≤ 1/2)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (p : Ω × Rotation (Point d))
    (hgood : p ∉ projectionBadEvent hN (fun i => U (blockUnit i (1:ℝ)))
      (radialPolicyStages (T := T) query A β b R N output) (2*R) t) :
    responseHistory query (fun _ (_ : Unit) => fullJet
      (radialGlobalization (curvatureFrameCore (rotatedEmbedding U p.2) A β) b R)) p.1 () N =
    responseHistory query (radialPrefixOracle (rotatedEmbedding U p.2) A β b R) p.1 () N := by
  apply radialPrefix_transcript_coupling query _ A β b hR p.1 N hN.le
  intro n hn hball i hi
  let r : Fin N := ⟨n, hn⟩
  have hid := radialPolicyStages_query_identity hN query U p.2 A β b R output p.1 r
  have hb : ‖radialPolicyStages (T := T) query A β b R N output r.castSucc
      (p.1, fun k => isometry (Point d) p.2 (U (blockUnit (prefixIndex hN r.castSucc k) (1:ℝ))))‖ ≤
        2*R := by rw [hid]; exact hball
  have hp := projection_lt_of_not_bad hN (fun i => U (blockUnit i (1:ℝ)))
    (radialPolicyStages (T := T) query A β b R N output) (2*R) t p hgood r.castSucc i
    (by dsimp [r]; omega) hb
  rw [hid] at hp
  rw [curvatureFrameMap_coordinate, abs_mul, abs_of_nonneg hβ, rotatedEmbedding_column]
  rw [real_inner_comm]
  exact (mul_le_mul_of_nonneg_left hp.le hβ).trans hβt

end SampleReuse.RandomFrame
