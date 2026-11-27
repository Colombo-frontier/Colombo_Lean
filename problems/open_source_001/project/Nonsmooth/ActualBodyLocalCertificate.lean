import Nonsmooth.LocalizationBody
import Nonsmooth.NormalizedLocalCertificate
import Nonsmooth.BodyPullbackGeometry

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A body alone determines feasible local queries and a valid next body for every discrete history. -/
theorem actual_body_local_certificate {R : ℝ} (B : LocalizationBody E R)
    (hd : 2 ≤ Module.finrank ℝ E) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E R),
      ∃ out : CircularHistory → Feasible E R, ∃ next : CircularHistory → LocalizationBody E R,
      p.IsMeasurable ∧ (∀ st, p.output () st = out st.1) ∧ Measurable out ∧
      (T : ℝ) ≤ 434 * (Module.finrank ℝ E : ℝ) * Real.log ((Module.finrank ℝ E : ℝ) + 1) ∧
      (∀ h, (next h).carrier ⊆ B.carrier) ∧
      ∀ f : E → ℝ, ConvexOn ℝ B.carrier f →
        let st := p.run (fun z => f z.val) () T
        (∀ z ∈ B.carrier, f z < f (p.result (fun z => f z.val) () T).val → z ∈ (next st.1).carrier) ∧
        volume (next st.1).carrier + ENNReal.ofReal (1 / 8 : ℝ) * volume B.carrier ≤ volume B.carrier := by
  obtain ⟨c, _hc, L, hconv, hcompact, hinner, houter, hdepth⟩ :=
    exists_general_body_normalization B.convex B.compact B.interior_nonempty
  let G := L '' centeredBody c B.carrier
  let Q := bodyPullback c L
  have hQG : Q '' G = B.carrier := bodyPullback_image_normalized c L B.carrier
  obtain ⟨T, p, out, cut, hp, hout, houtm, hT, hvalid, hcert⟩ :=
    actual_normalized_local_certificate hconv hcompact hd hinner houter hdepth
  let q : Feasible E (1 / (Module.finrank ℝ E : ℝ)) → Feasible E R := fun z =>
    ⟨Q z.val, by
      have hzG : z.val ∈ G := hinner (by simpa using z.property)
      have hzK : Q z.val ∈ B.carrier := hQG ▸ mem_image_of_mem Q hzG
      simpa using B.feasible hzK⟩
  have hqm : Measurable q :=
    (Q.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  let next : CircularHistory → LocalizationBody E R := fun h =>
    { carrier := Q '' cut h
      convex := bodyPullback_convex c L (hvalid h).2.1
      compact := (hvalid h).2.2.1.image Q.continuous
      interior_nonempty := by
        rw [← Q.image_interior]
        exact ⟨Q 0, ⟨0, (hvalid h).2.2.2, rfl⟩⟩
      feasible := by
        have hsub : Q '' cut h ⊆ B.carrier := hQG ▸ image_mono (hvalid h).1
        exact hsub.trans B.feasible }
  let p' := p.simulate q (fun _ y => y)
  refine ⟨T, p', fun h => q (out h), next, simulation_measurable hp hqm measurable_snd,
    ?_, hqm.comp houtm, hT, ?_, ?_⟩
  · intro st
    change q (p.output () st) = q (out st.1)
    rw [hout st]
  · intro h
    exact hQG ▸ image_mono (hvalid h).1
  · intro f hf
    let F := fun z : E => f (Q z)
    have hF : ConvexOn ℝ G F := convexOn_bodyPullback c L hf
    obtain ⟨hkeep, hvol⟩ := hcert F hF
    have hs : p'.run (fun z => f z.val) () T = p.run (fun z => F z.val) () T :=
      simulation_run_exact p q (fun _ y => y) (fun z => f z.val) (fun z => F z.val)
        (fun _ => rfl) () T
    have hres : p'.result (fun z => f z.val) () T = q (p.result (fun z => F z.val) () T) :=
      simulation_output_exact p q (fun _ y => y) (fun z => f z.val) (fun z => F z.val)
        (fun _ => rfl) () T
    dsimp only
    rw [hs, hres]
    constructor
    · intro z hz hbetter
      have hzG : Q.symm z ∈ G := by
        have hz' : z ∈ Q '' G := hQG ▸ hz
        obtain ⟨w, hw, rfl⟩ := hz'
        simpa using hw
      have hzcut := hkeep (Q.symm z) hzG (by simpa only [F, Q.apply_symm_apply] using hbetter)
      exact ⟨Q.symm z, hzcut, Q.apply_symm_apply z⟩
    · have h := (bodyPullback_volume_fraction_iff c L G
        (cut (p.run (fun z => F z.val) () T).1) (ENNReal.ofReal (1 / 8 : ℝ))).mpr hvol
      rw [bodyPullback_image_normalized] at h
      exact h

end
end Nonsmooth
