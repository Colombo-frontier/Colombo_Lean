import Bilevel.StoredGenieProtocol
import Bilevel.GenieMeasurable
import Bilevel.ProjectionObservationMeasurable

/-! Measurable raw query/revelation rules automatically satisfy the probability theorem's Borel condition. -/
noncomputable section
open MeasureTheory
namespace Bilevel.RawGenieProtocol
open EuclideanGaussian ProjectionPosterior ProjectionObservation

abbrev State (d T : ℕ) := ProjectionStore.Store d × Frame d T

structure MeasurableFamily {d T m r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → RawGenieProtocol.Protocol d T m r) : Prop where
  normalized : GenieProtocol.MeasurableFamily
    (fun p : Ω × State d T => normalizeStored (P p.1) p.2.1 p.2.2)

namespace MeasurableFamily
variable {d T m r : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem halt : MeasurableFamily (fun _ : Ω => (Protocol.halt : Protocol d T m r)) :=
  ⟨GenieProtocol.MeasurableFamily.halt⟩

theorem comap {P : Ω → Protocol d T m r} (hP : MeasurableFamily P)
    (f : Ω' → Ω) (hf : Measurable f) : MeasurableFamily (fun ω => P (f ω)) := by
  exact ⟨hP.normalized.comap (fun p : Ω' × State d T => (f p.1,p.2)) (hf.prodMap measurable_id)⟩

theorem query (q : Ω → Space d) (hq : Measurable q)
    (next : Ω × Frame d T → Protocol d T m r) (hnext : MeasurableFamily next) :
    MeasurableFamily (fun ω => Protocol.query (q ω) (fun Z => next (ω,Z))) := by
  classical
  let A : Ω × State d T → ProjectionStore.Store d := fun p => p.2.1
  let Z : Ω × State d T → Frame d T := fun p => p.2.2
  let q' : Ω × State d T → Space d := fun p => q p.1
  have hA : Measurable A := measurable_fst.comp measurable_snd
  have hZ : Measurable Z := measurable_snd.comp measurable_snd
  have hq' : Measurable q' := hq.comp measurable_fst
  let w := fun p => ProjectionStore.direction d (A p) (q' p)
  have hw : Measurable w := ProjectionStore.direction_measurable d A hA q' hq'
  let ins := fun p => ProjectionStore.insert d (A p) (q' p)
  have hins : Measurable ins := ProjectionStore.insert_measurable d A hA q' hq'
  let upd := fun p : (Ω × State d T) × (Fin T → ℝ) => queryUpdate d T (Z p.1) (w p.1) p.2
  have hupd : Measurable upd := query_update_measurable d T _ (hZ.comp measurable_fst)
    _ (hw.comp measurable_fst) _ measurable_snd
  have hn := hnext.normalized.comap
    (fun p : (Ω × State d T) × (Fin T → ℝ) => ((p.1.1,upd p),(ins p.1,upd p)))
    (((measurable_fst.comp measurable_fst).prodMk hupd).prodMk
      ((hins.comp measurable_fst).prodMk hupd))
  have hnonzero := GenieProtocol.MeasurableFamily.query w hw _ hn
  have hz := (hnext.normalized.comap
    (fun p : Ω × State d T => ((p.1,Z p),(A p,Z p)))
    ((measurable_fst.prodMk hZ).prodMk (hA.prodMk hZ))).addQuery
  let s := {p : Ω × State d T | ProjectionStore.residual d (A p) (q' p) = 0}
  have hs : MeasurableSet s := (ProjectionStore.residual_measurable d A hA q' hq') (measurableSet_singleton 0)
  refine ⟨?_⟩
  convert hz.piecewise hnonzero s hs using 1
  funext p
  by_cases hp : ProjectionStore.residual d (A p) (q' p) = 0
  · simp [normalizeStored,Set.piecewise,s,A,Z,q',hp]
  · simp [normalizeStored,Set.piecewise,s,A,Z,q',w,ins,upd,hp]

theorem reveal (j : Ω → Fin T) (hj : Measurable j)
    (next : Ω × (Space d × Frame d T) → Protocol d T m r) (hnext : MeasurableFamily next) :
    MeasurableFamily (fun ω => Protocol.reveal (j ω) (fun z => next (ω,z))) := by
  let upd := fun p : (Ω × State d T) × Space d => revealUpdate d T p.1.2.2 (j p.1.1) p.2
  have hupd : Measurable upd := reveal_update_measurable d T _
    (measurable_snd.comp (measurable_snd.comp measurable_fst)) _
    (hj.comp (measurable_fst.comp measurable_fst)) _ measurable_snd
  let ins := fun p : (Ω × State d T) × Space d => ProjectionStore.insert d p.1.2.1 p.2
  have hins : Measurable ins := ProjectionStore.insert_measurable d _
    (measurable_fst.comp (measurable_snd.comp measurable_fst)) _ measurable_snd
  have hn := hnext.normalized.comap
    (fun p : (Ω × State d T) × Space d => ((p.1.1,(p.2,upd p)),(ins p,upd p)))
    (((measurable_fst.comp measurable_fst).prodMk (measurable_snd.prodMk hupd)).prodMk
      (hins.prodMk hupd))
  exact ⟨GenieProtocol.MeasurableFamily.reveal (fun p : Ω × State d T => j p.1)
    (hj.comp measurable_fst) _ hn⟩

theorem regular {P : Ω → Protocol d T m r} (hP : MeasurableFamily P)
    (ω : Ω) (V : Submodule ℝ (Space d)) (Z : Frame d T) (b : ℝ) :
    GenieProtocol.Regular b (normalize (P ω) V Z) := by
  have h := hP.normalized.regular b (ω,(ProjectionStore.ofSubspace d V,Z))
  rwa [stored_eq_normalize] at h

open Classical in
theorem piecewise {P Q : Ω → Protocol d T m r} (hP : MeasurableFamily P)
    (hQ : MeasurableFamily Q) (s : Set Ω) (hs : MeasurableSet s) :
    MeasurableFamily (s.piecewise P Q) := by
  classical
  have h := hP.normalized.piecewise hQ.normalized {p : Ω × State d T | p.1 ∈ s} (measurable_fst hs)
  refine ⟨?_⟩
  convert h using 1
  funext p
  by_cases hp : p.1 ∈ s <;> simp [Set.piecewise,hp]

end MeasurableFamily
end Bilevel.RawGenieProtocol
