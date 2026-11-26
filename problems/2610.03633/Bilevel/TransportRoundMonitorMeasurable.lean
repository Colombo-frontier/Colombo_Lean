import Bilevel.TransportRoundLedgerMeasurable
import Bilevel.TransportRoundBatchEnergy

/-! The concrete forward/reverse ledger failure events are Borel. Only the
measurable physical paired-domain/range stores are needed; no sigma-algebra
containing undisclosed frame information is substituted for the transcript. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior OrthogonalAction
set_option maxHeartbeats 800000

theorem frame_layer_measurable {Ω : Type*} [MeasurableSpace Ω] {n D T : ℕ} (hT : T≤D)
    (z : Ω → Latent n D) (hz : Measurable z) (v : Vertex n) :
    Measurable (fun ω => frame T hT (z ω) v) :=
  (measurable_pi_apply v).comp ((frame_measurable n D T hT).comp hz)

theorem forwardMonitor_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (P : Ω → Edge n → Pairs D)
    (hP : ∀ e,Measurable (fun ω => ProjectionStore.ofSubspace D (domain (P ω e))))
    (W : Ω → Known n D) (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) (e : Edge n) :
    MeasurableSet {ω | forwardMonitor hT t (g ω) (z ω) (P ω) (W ω) e} := by
  have hV := frame_layer_measurable hT z hz (src e)
  have hH := span_projector_measurable _ hV
  have hK := protectedSpace_projector_measurable _ hV (oldProtected T t (src e))
  have hA := sup_projector_measurable _ _ (hP e) hK
  have hFull : Measurable (fun ω => ProjectionStore.ofSubspace D (domain (hardPairs T hT e (z ω)++P ω e))) := by
    have hh := sup_projector_measurable _ _ hH (hP e)
    simpa only [domain_append,hardPairs_domain] using hh
  have hInput := residualSpace_projector_measurable _ _ hA (known_projector_measurable g hg (src e))
  have hFresh := residualSpace_projector_measurable _ _ hFull hInput
  exact TransportControllerOperator.angleBad_store_measurable D _ _ (hW (dst e)) hFresh
    (fun ω => (z ω).2 e) ((measurable_pi_apply e).comp (measurable_snd.comp hz))

theorem reverseHardPairs_domain {n D T : ℕ} (hT : T≤D) (e : Edge n) (z : Latent n D) :
    domain (reverseHardPairs T hT e z)=frameSpace (frame T hT z (dst e)) :=
  TransportControllerPairedStore.domain_pairs (frame T hT z (dst e),frame T hT z (src e))

theorem reverseMonitor_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (P : Ω → Edge n → Pairs D)
    (hP : ∀ e,Measurable (fun ω => ProjectionStore.ofSubspace D (range (P ω e))))
    (W : Ω → Known n D) (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) (e : Edge n) :
    MeasurableSet {ω | reverseMonitor hT t (g ω) (z ω) (P ω) (W ω) e} := by
  have hV := frame_layer_measurable hT z hz (dst e)
  have hH := span_projector_measurable _ hV
  have hK := protectedSpace_projector_measurable _ hV (oldProtected T t (src e))
  have hO : Measurable (fun ω => (z ω).2 e) := (measurable_pi_apply e).comp (measurable_snd.comp hz)
  have hImage := map_projector_measurable _ (known_projector_measurable g hg (src e)) _ hO
  have hPair : Measurable (fun ω => ProjectionStore.ofSubspace D (domain (swapPairs (forwardPairs e (g ω) (z ω)++P ω e)))) := by
    have hh := sup_projector_measurable _ _ hImage (hP e)
    simpa only [swapPairs_domain,range_append,forwardPairs_range] using hh
  have hA := sup_projector_measurable _ _ hPair hK
  have hFull : Measurable (fun ω => ProjectionStore.ofSubspace D
      (domain (reverseHardPairs T hT e (z ω)++swapPairs (forwardPairs e (g ω) (z ω)++P ω e)))) := by
    have hh := sup_projector_measurable _ _ hH hPair
    simpa only [domain_append,reverseHardPairs_domain] using hh
  have hInput := residualSpace_projector_measurable _ _ hA (known_projector_measurable g hg (dst e))
  have hFresh := residualSpace_projector_measurable _ _ hFull hInput
  exact TransportControllerOperator.angleBad_store_measurable D _ _ (hW (src e)) hFresh _ hO.inv

theorem forwardFailure_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (P : Ω → Edge n → Pairs D)
    (hP : ∀ e,Measurable (fun ω => ProjectionStore.ofSubspace D (domain (P ω e))))
    (es : List (Edge n)) (W : Ω → Known n D)
    (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) :
    MeasurableSet {ω | forwardFailure hT t (g ω) (z ω) (P ω) es (W ω)} := by
  induction es generalizing W with
  | nil => exact MeasurableSet.empty
  | cons e es ih =>
    apply (forwardMonitor_measurable hT t g hg z hz P hP W hW e).union
    have hS := map_projector_measurable _ (known_projector_measurable g hg (src e))
      (fun ω => (z ω).2 e) ((measurable_pi_apply e).comp (measurable_snd.comp hz))
    exact ih _ (mergeBlock_projector_measurable W hW (dst e) _ hS)

theorem reverseFailure_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (P : Ω → Edge n → Pairs D)
    (hP : ∀ e,Measurable (fun ω => ProjectionStore.ofSubspace D (range (P ω e))))
    (es : List (Edge n)) (W : Ω → Known n D)
    (hW : ∀ v,Measurable (fun ω => ProjectionStore.ofSubspace D (W ω v))) :
    MeasurableSet {ω | reverseFailure hT t (g ω) (z ω) (P ω) es (W ω)} := by
  induction es generalizing W with
  | nil => exact MeasurableSet.empty
  | cons e es ih =>
    apply (reverseMonitor_measurable hT t g hg z hz P hP W hW e).union
    have hS := map_projector_measurable _ (known_projector_measurable g hg (dst e))
      (fun ω => ((z ω).2 e)⁻¹) (((measurable_pi_apply e).comp (measurable_snd.comp hz)).inv)
    exact ih _ (mergeBlock_projector_measurable W hW (src e) _ hS)

theorem batchFailure_measurable {Ω : Type*} [MeasurableSpace Ω] {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Ω → Generators n D m) (hg : Measurable g) (z : Ω → Latent n D) (hz : Measurable z)
    (P : Ω → Edge n → Pairs D)
    (hdom : ∀ e,Measurable (fun ω => ProjectionStore.ofSubspace D (domain (P ω e))))
    (hran : ∀ e,Measurable (fun ω => ProjectionStore.ofSubspace D (range (P ω e)))) :
    MeasurableSet {ω | batchFailure hT t (g ω) (z ω) (P ω)} := by
  have hG := postGrant_measurable hT t g hg z hz
  have hW := known_projector_measurable _ hG
  exact (forwardFailure_measurable hT t g hg z hz P hdom _ _ hW).union
    (reverseFailure_measurable hT t g hg z hz P hran _ _ (forwardLedger_projector_measurable g hg z hz _ hW))

end Bilevel.TransportRound
