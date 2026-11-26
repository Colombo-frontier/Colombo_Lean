import SampleReuse.RandomFrameBadEvent

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory SecondOrder RandomizedFO2003 Rotations
open scoped InnerProductSpace

variable {Ω : Type*}

def radialFullOutput {d T : ℕ}
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b R : ℝ) (N : ℕ)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d) (ω : Ω) :=
  output ω (responseHistory query
    (fun _ (_ : Unit) => fullJet (radialGlobalization (curvatureFrameCore U A β) b R)) ω () N)

theorem radialPolicyStages_output_identity {d T N : ℕ} (hN : N < T+1)
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (V : Rotation (Point d)) (A β b R : ℝ)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d) (ω : Ω) :
    radialPolicyStages (T := T) query A β b R N output (Fin.last N)
      (ω, fun k => isometry (Point d) V (U (blockUnit (prefixIndex hN (Fin.last N) k) (1:ℝ)))) =
    output ω (responseHistory query (radialPrefixOracle (rotatedEmbedding U V) A β b R) ω () N) := by
  change policyStages query _ N output (Fin.last N) _ = _
  rw [policyStages_output, radialPrefixOracle, responseHistory_eq_prefixHistory]
  exact congrArg (fun z => output ω (prefixHistory query
    (fun n => prefixRadialReply (d := d) T n A β b R) ω N z))
      (rotated_columns_prefix hN U V (Fin.last N)).symm

/-- This reduction consumes only a deterministic analytic necessary condition
for SOSP. All probability, unrestricted full-jet execution, adaptivity, and
output coupling are discharged here by the actual Haar frame construction. -/
theorem radial_success_subset_bad {d T N : ℕ} (hN : N < T+1)
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b ε γ : ℝ) {R t : ℝ}
    (hR : 0 < R) (hβ : 0 ≤ β) (hβt : β*t ≤ 1/2)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (hnecessary : ∀ V : Rotation (Point d), ∀ x : Point d,
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U V) A β) b R) ε γ x →
        ‖x‖ < R ∧ ∀ i : Fin (T+1), 1 < |curvatureFrameMap (rotatedEmbedding U V) β x i|) :
    {p : Ω × Rotation (Point d) |
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U p.2) A β) b R) ε γ
        (radialFullOutput query (rotatedEmbedding U p.2) A β b R N output p.1)} ⊆
    projectionBadEvent hN (fun i => U (blockUnit i (1:ℝ)))
      (radialPolicyStages (T := T) query A β b R N output) (2*R) t := by
  intro p hs
  by_contra hgood
  obtain ⟨hinside, hcoords⟩ := hnecessary p.2 _ hs
  have hc := radial_full_transcript_eq_on_good hN query U A β b hR hβ hβt output p hgood
  have hout := congrArg (output p.1) hc
  have hid := radialPolicyStages_output_identity hN query U p.2 A β b R output p.1
  have hval : radialPolicyStages (T := T) query A β b R N output (Fin.last N)
      (p.1, fun k => isometry (Point d) p.2
        (U (blockUnit (prefixIndex hN (Fin.last N) k) (1:ℝ)))) =
      radialFullOutput query (rotatedEmbedding U p.2) A β b R N output p.1 :=
    hid.trans hout.symm
  have hball : ‖radialPolicyStages (T := T) query A β b R N output (Fin.last N)
      (p.1, fun k => isometry (Point d) p.2
        (U (blockUnit (prefixIndex hN (Fin.last N) k) (1:ℝ))))‖ ≤ 2*R := by
    rw [hval]
    linarith
  let j : Fin (T+1) := ⟨N,hN⟩
  have hp := projection_lt_of_not_bad hN (fun i => U (blockUnit i (1:ℝ)))
    (radialPolicyStages (T := T) query A β b R N output) (2*R) t p hgood (Fin.last N) j le_rfl hball
  rw [hval] at hp
  have hcoord : |curvatureFrameMap (rotatedEmbedding U p.2) β
      (radialFullOutput query (rotatedEmbedding U p.2) A β b R N output p.1) j| ≤ 1/2 := by
    rw [curvatureFrameMap_coordinate, abs_mul, abs_of_nonneg hβ, rotatedEmbedding_column,
      real_inner_comm]
    exact (mul_le_mul_of_nonneg_left hp.le hβ).trans hβt
  have hgt := hcoords j
  linarith

variable [MeasurableSpace Ω]

theorem radial_fixed_cap_success_bound {d T N : ℕ} (hN : N < T+1)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      query n p.1 p.2))
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) (A β b ε γ : ℝ) {R t : ℝ}
    (hR : 0 < R) (ht : 0 < t) (hβ : 0 ≤ β) (hβt : β*t ≤ 1/2)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (ho : Measurable (fun p : Ω × (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      output p.1 p.2))
    (hnecessary : ∀ V : Rotation (Point d), ∀ x : Point d,
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U V) A β) b R) ε γ x →
        ‖x‖ < R ∧ ∀ i : Fin (T+1), 1 < |curvatureFrameMap (rotatedEmbedding U V) β x i|) :
    (μ.prod (haarLaw (Point d))).real {p |
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U p.2) A β) b R) ε γ
        (radialFullOutput query (rotatedEmbedding U p.2) A β b R N output p.1)} ≤
      (((T+1 : ℕ) : ℝ) * (N+1)) *
        (2 * Real.exp (-((d-N : ℕ) : ℝ) * t ^ 2 / (2 * (2*R) ^ 2))) := by
  apply (measureReal_mono (μ := μ.prod (haarLaw (Point d)))
    (radial_success_subset_bad hN query U A β b ε γ hR hβ hβt output hnecessary)).trans
  have hb := projectionBadEvent_bound hN μ (fun i => U (blockUnit i (1:ℝ)))
    (embedding_columns_orthonormal U) (radialPolicyStages (T := T) query A β b R N output)
    (measurable_radialPolicyStages query hq A β b hR N output ho) (by positivity : 0 < 2*R) ht
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hb

end SampleReuse.RandomFrame
