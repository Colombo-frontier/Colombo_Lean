import HaarRebalancing
import AdaptiveSphereConditional

/-!
Actual product-prior symmetries, with an arbitrary independent private seed.
The skew transformation may depend measurably on the seed; it is proved
measure preserving from Haar invariance rather than postulated as a posterior
moment. The adaptive-history extension is not asserted by this file.
-/

open MeasureTheory ProbabilityTheory Set

namespace Task006.AdaptiveSphere

noncomputable section

section SeedSkew

variable {S G : Type*} [MeasurableSpace S] [MeasurableSpace G]
  [Group G] [MeasurableMul₂ G] [MeasurableInv G]

/-- A measurable seed-dependent left multiplication is a measurable equivalence. -/
def seedLeftEquiv (a : S → G) (ha : Measurable a) : S × G ≃ᵐ S × G where
  toFun z := (z.1, a z.1 * z.2)
  invFun z := (z.1, (a z.1)⁻¹ * z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk ((ha.comp measurable_fst).mul measurable_snd)
  measurable_invFun := measurable_fst.prodMk (((ha.comp measurable_fst).inv).mul measurable_snd)

/-- This genuinely preserves an independent seed/Haar product law. -/
theorem seedLeftEquiv_measurePreserving
    (sigma : Measure S) (mu : Measure G) [SFinite sigma] [SFinite mu]
    [Measure.IsMulLeftInvariant mu] (a : S → G) (ha : Measurable a) :
    MeasurePreserving (seedLeftEquiv a ha) (sigma.prod mu) (sigma.prod mu) := by
  exact (MeasurePreserving.id sigma).skew_product
    ((ha.comp measurable_fst).mul measurable_snd)
    (Filter.Eventually.of_forall fun s => map_mul_left_eq_self mu (a s))

/-- Conditional transport through a seed-dependent Haar symmetry which fixes
an actual measurable observable. -/
theorem seedLeft_condExp_transport
    (sigma : Measure S) (mu : Measure G) [IsProbabilityMeasure sigma]
    [IsProbabilityMeasure mu] [Measure.IsMulLeftInvariant mu]
    (a : S → G) (ha : Measurable a)
    {H : Type*} [mH : MeasurableSpace H]
    (obs : S × G → H) (hobs : Measurable obs)
    (hobsfix : ∀ z, obs (seedLeftEquiv a ha z) = obs z)
    (f g : S × G → ℝ) (hf : Integrable f (sigma.prod mu))
    (hg : Integrable g (sigma.prod mu))
    (hcomp : ∀ z, f (seedLeftEquiv a ha z) = g z) :
    (sigma.prod mu)[f | mH.comap obs] =ᵐ[sigma.prod mu]
      (sigma.prod mu)[g | mH.comap obs] := by
  exact condExp_transport_of_invariant_equiv (mH.comap obs) hobs.comap_le
    (seedLeftEquiv a ha) (seedLeftEquiv_measurePreserving sigma mu a ha)
    (fun s hs => comap_event_invariant obs (seedLeftEquiv a ha) hobsfix hs)
    f g hf hg hcomp

end SeedSkew

section ActualHaarPrior

open Task006.HaarRebalancing

variable {S : Type*} [mS : MeasurableSpace S] {d : ℕ}

instance realMatrix_secondCountable (d : ℕ) :
    SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) := by
  change SecondCountableTopology (Fin d → Fin d → ℝ)
  infer_instance

instance orthogonalGroup_secondCountable (d : ℕ) :
    SecondCountableTopology (OrthogonalGroup d) := by
  change SecondCountableTopology (↥(unitary (Matrix (Fin d) (Fin d) ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ)))
  infer_instance

instance orthogonalGroup_jointMeasurableMul (d : ℕ) :
    MeasurableMul₂ (OrthogonalGroup d) where
  measurable_mul := by
    have hc : Continuous (fun p : OrthogonalGroup d × OrthogonalGroup d => p.1 * p.2) := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)
    exact hc.measurable

/-- Every integrable seed-dependent odd statistic of a genuine Haar sphere
vector has zero conditional mean given the independent private seed. -/
theorem haar_seed_condExp_odd
    (sigma : Measure S) [IsProbabilityMeasure sigma] (j : Fin d)
    (f : S → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Integrable (fun z : S × OrthogonalGroup d => f z.1 (column z.2 j))
      (sigma.prod (orthogonalHaarProbability d)))
    (hodd : ∀ s x, f s (-x) = -f s x) :
    (sigma.prod (orthogonalHaarProbability d))[
      (fun z : S × OrthogonalGroup d => f z.1 (column z.2 j)) |
        mS.comap Prod.fst] =ᵐ[sigma.prod (orthogonalHaarProbability d)]
      (fun _ => (0 : ℝ)) := by
  let U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearIsometryEquiv.neg ℝ
  let a : S → OrthogonalGroup d := fun _ => orthogonalMatrixOfLinearIsometryEquiv U
  have ha : Measurable a := measurable_const
  let e := seedLeftEquiv a ha
  have he := seedLeftEquiv_measurePreserving sigma (orthogonalHaarProbability d) a ha
  apply condExp_zero_of_invariant_odd (mS.comap Prod.fst) measurable_fst.comap_le e he
    (fun s hs => comap_event_invariant Prod.fst e (by intro z; rfl) hs)
    (fun z : S × OrthogonalGroup d => f z.1 (column z.2 j)) hf
  intro z
  change f z.1 (column (orthogonalMatrixOfLinearIsometryEquiv U * z.2) j) =
    -f z.1 (column z.2 j)
  rw [column_mul_orthogonalMatrixOfLinearIsometryEquiv]
  simpa [U] using hodd z.1 (column z.2 j)

/-- In particular the first adaptive linear measurement, whose direction is
an arbitrary measurable function of the private seed, is conditionally centered. -/
theorem haar_initial_condExp_projection_zero
    (sigma : Measure S) [IsProbabilityMeasure sigma] (j : Fin d)
    (u : S → EuclideanSpace ℝ (Fin d)) (hu : Measurable u)
    (B : ℝ) (hB : ∀ s, ‖u s‖ ≤ B) :
    (sigma.prod (orthogonalHaarProbability d))[
      (fun z : S × OrthogonalGroup d => inner ℝ (column z.2 j) (u z.1)) |
        mS.comap Prod.fst] =ᵐ[sigma.prod (orthogonalHaarProbability d)]
      (fun _ => (0 : ℝ)) := by
  have hmeas : Measurable
      (fun z : S × OrthogonalGroup d => inner ℝ (column z.2 j) (u z.1)) := by
    exact ((measurable_column j).comp measurable_snd).inner (hu.comp measurable_fst)
  have hint : Integrable
      (fun z : S × OrthogonalGroup d => inner ℝ (column z.2 j) (u z.1))
      (sigma.prod (orthogonalHaarProbability d)) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable B
    filter_upwards [] with z
    have hc : ‖column z.2 j‖ = 1 := (orthonormal_column z.2).norm_eq_one j
    calc
      ‖inner ℝ (column z.2 j) (u z.1)‖ ≤ ‖column z.2 j‖ * ‖u z.1‖ :=
        norm_inner_le_norm (𝕜 := ℝ) _ _
      _ ≤ B := by rw [hc, one_mul]; exact hB z.1
  exact haar_seed_condExp_odd sigma j (fun s x => inner ℝ x (u s)) hint
    (by intro s x; simp)

#print axioms seedLeftEquiv_measurePreserving
#print axioms seedLeft_condExp_transport
#print axioms haar_seed_condExp_odd
#print axioms haar_initial_condExp_projection_zero

end ActualHaarPrior
end
end Task006.AdaptiveSphere
