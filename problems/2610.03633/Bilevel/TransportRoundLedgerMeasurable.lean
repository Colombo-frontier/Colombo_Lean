import Bilevel.TransportRoundProjectorOperations
import Bilevel.TransportRoundReverseLedger

/-! Joint Borel measurability of the actual analysis ledgers. These lemmas
are uniform in a measurable parameter, allowing full conditioned contexts,
entering transcripts, and independent private memory to be used as inputs. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 800000

theorem mergeBlock_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {n D : ℕ}
    (W : Ω → Known n D) (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v)))
    (v : Vertex n) (S : Ω → Submodule ℝ (Space D))
    (hS : Measurable (fun ω => ProjectionStore.ofSubspace D (S ω))) :
    ∀ w,Measurable (fun ω => ProjectionStore.ofSubspace D (mergeBlock (W ω) (v,S ω) w)) := by
  intro w
  by_cases hw : w=v
  · subst w
    simp only [mergeBlock,Function.update_self]
    exact sup_projector_measurable _ _ (hW v) hS
  · simpa only [mergeBlock,Function.update_of_ne hw] using hW w

theorem known_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m : ℕ}
    (g : Ω → Generators n D m) (hg : Measurable g) (v : Vertex n) :
    Measurable (fun ω => ProjectionStore.ofSubspace D (known (g ω) v)) :=
  span_projector_measurable _ ((measurable_pi_apply v).comp hg)

theorem postGrant_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z) :
    Measurable (fun ω => postGrant T hT t (g ω) (z ω)) :=
  (augment_measurable n D m 1).comp (hg.prodMk
    ((disclosures_measurable T hT (fun v (_ : Fin 1) => postNew t v)).comp hz))

theorem forwardAlong_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m : ℕ}
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (es : List (Edge n)) (W : Ω → Known n D)
    (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) :
    ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (forwardAlong (g ω) (z ω) es (W ω) v)) := by
  induction es generalizing W with
  | nil => exact hW
  | cons e es ih =>
    have hO : Measurable (fun ω => (z ω).2 e) := (measurable_pi_apply e).comp (measurable_snd.comp hz)
    have hS := map_projector_measurable (fun ω => known (g ω) (src e)) (known_projector_measurable g hg (src e)) _ hO
    exact ih (fun ω => mergeBlock (W ω) (forwardBlock (g ω) (z ω) e))
      (mergeBlock_projector_measurable W hW (dst e) _ hS)

theorem reverseAlong_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m : ℕ}
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (es : List (Edge n)) (W : Ω → Known n D)
    (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) :
    ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (reverseAlong (g ω) (z ω) es (W ω) v)) := by
  induction es generalizing W with
  | nil => exact hW
  | cons e es ih =>
    have hO : Measurable (fun ω => ((z ω).2 e)⁻¹) := ((measurable_pi_apply e).comp (measurable_snd.comp hz)).inv
    have hS := map_projector_measurable (fun ω => known (g ω) (dst e)) (known_projector_measurable g hg (dst e)) _ hO
    exact ih (fun ω => mergeBlock (W ω) (reverseBlock (g ω) (z ω) e))
      (mergeBlock_projector_measurable W hW (src e) _ hS)

theorem forwardLedger_projector_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m : ℕ}
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (W : Ω → Known n D) (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) :
    ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (forwardLedger (g ω) (z ω) (W ω) v)) := by
  have hh := forwardAlong_projector_measurable g hg z hz (List.ofFn (fun e : Edge n => e)) W hW
  simpa only [forwardAlong_all] using hh

end Bilevel.TransportRound
