import Bilevel.TransportNetworkEdgeGauge
import Bilevel.TransportEdgePairs

/-! The actual full-frame/other-edge posterior initializes a supported paired
history and its residual left isotropy for the current edge. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

def hardPairs {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) (z : Latent n d) :
    TransportEdgePosterior.Pairs d :=
  List.ofFn (fun i : Fin T => (frame T hT z (src e) i,frame T hT z (dst e) i))

theorem pair_output_mem {D : ℕ} (L : TransportEdgePosterior.Pairs D)
    (a b : Space D) (hp : (a,b) ∈ L) : b ∈ TransportEdgePosterior.range L := by
  induction L with
  | nil => simp only [List.not_mem_nil] at hp
  | cons p L ih =>
    rcases List.mem_cons.mp hp with h | h
    · cases h
      exact (show Submodule.span ℝ {b} ≤ TransportEdgePosterior.range L ⊔ Submodule.span ℝ {b}
        from le_sup_right) (Submodule.mem_span_singleton_self b)
    · exact (show TransportEdgePosterior.range L ≤ TransportEdgePosterior.range L ⊔
        Submodule.span ℝ {p.2} from le_sup_left) (ih h)

theorem supports_iff_pairs {D : ℕ} (L : TransportEdgePosterior.Pairs D) (O : OrthogonalHaar.Group D) :
    TransportEdgePosterior.Supports L O ↔ ∀ p ∈ L, O • p.1 = p.2 := by
  induction L with
  | nil => simp [TransportEdgePosterior.Supports]
  | cons p L ih =>
    rcases p with ⟨a,b⟩
    simpa only [TransportEdgePosterior.Supports,List.forall_mem_cons,Prod.fst,Prod.snd] using
      (and_congr_right (fun _ => ih))

theorem hardPairs_output_mem {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n)
    (z : Latent n d) (i : Fin T) :
    frame T hT z (dst e) i ∈ TransportEdgePosterior.range (hardPairs T hT e z) := by
  apply pair_output_mem _ (frame T hT z (src e) i) _
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

def edgePosterior {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) (z₀ : Latent n d) :
    Measure (OrthogonalHaar.Group d) :=
  (condDistrib id (context T hT e) (law n d) (context T hT e z₀)).map (fun z => z.2 e)

instance edgePosterior_probability {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) (z₀ : Latent n d) :
    IsProbabilityMeasure (edgePosterior T hT e z₀) :=
  isProbabilityMeasure_map (((measurable_pi_apply e).comp measurable_snd).aemeasurable)

theorem edgePosterior_supported {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) :
    ∀ᵐ z₀ ∂law n d, ∀ᵐ O ∂edgePosterior T hT e z₀,
      TransportEdgePosterior.Supports (hardPairs T hT e z₀) O := by
  have hp := ae_of_ae_map (context_measurable T hT e).aemeasurable (context_posterior_fiber T hT e)
  filter_upwards [hp] with z₀ hz₀
  apply (ae_map_iff (((measurable_pi_apply e).comp measurable_snd).aemeasurable)
    (TransportEdgePosterior.support_measurable (hardPairs T hT e z₀))).mpr
  filter_upwards [hz₀] with z hz
  apply (supports_iff_pairs _ _).mpr
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  have hs := congrArg (fun c : Context (d := d) e T => c.1 (src e) i) hz
  have ht := congrArg (fun c : Context (d := d) e T => c.1 (dst e) i) hz
  change frame T hT z (src e) i = frame T hT z₀ (src e) i at hs
  change frame T hT z (dst e) i = frame T hT z₀ (dst e) i at ht
  simpa only [hs,ht] using edge_frame T hT z e i

theorem edgePosterior_initialized {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) :
    ∀ᵐ z₀ ∂law n d,
      TransportEdgePosterior.Invariant (TransportEdgePosterior.range (hardPairs T hT e z₀))
        (edgePosterior T hT e z₀) ∧
      (∀ᵐ O ∂edgePosterior T hT e z₀, TransportEdgePosterior.Supports (hardPairs T hT e z₀) O) := by
  filter_upwards [context_edge_posterior_left T hT e,edgePosterior_supported T hT e] with z₀ hz₀ hs
  refine ⟨?_,hs⟩
  intro S
  apply hz₀ S.val
  intro i
  exact (ProjectionStabilizer.membership d (TransportEdgePosterior.range (hardPairs T hT e z₀))
    S.val).mp S.property _ (hardPairs_output_mem T hT e z₀ i)

end Bilevel.TransportNetwork
