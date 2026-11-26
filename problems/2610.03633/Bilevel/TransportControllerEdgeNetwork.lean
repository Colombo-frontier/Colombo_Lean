import Bilevel.TransportControllerEdge
import Bilevel.TransportAuxiliaryContext

/-! Paired-edge monitor bounds under the actual network-plus-auxiliary prior.
The monitor program is selected by the conditioned full context, not by the
unseen current edge. Its finite failure bound is then integrated back to the
original joint probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportControllerEdge
open EuclideanGaussian TransportNetwork TransportEdgePosterior
open TransportNetworkAuxiliary
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

theorem range_rank_length {D : ℕ} (L : Pairs D) : Module.finrank ℝ (range L) ≤ L.length := by
  induction L with
  | nil => simp [range]
  | cons p L ih => exact (range_rank_cons L p.1 p.2).trans (Nat.add_le_add_right ih 1)

theorem hardPairs_rank {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (z : Latent n D) :
    Module.finrank ℝ (range (hardPairs T hT e z)) ≤ T := by
  simpa only [hardPairs,List.length_ofFn] using range_rank_length (hardPairs T hT e z)

theorem conditional_network_angle_failure {n D k m : ℕ} {β : Type*}
    (T : ℕ) (hT : T ≤ D) (e : Edge n) (d r : ℕ) (hr : 0<r) (hD : T+m+r≤D)
    (P : FullContext (D := D) e T k → Program D β m)
    (hP : ∀ c, Regular (P c))
    (hV : ∀ s : Sample n D k, Valid d (P (fullContext T hT e s)) (hardPairs T hT e s.1)) :
    ∀ᵐ s ∂TransportNetworkAuxiliary.law n D k,
      TransportNetworkAuxiliary.edgePosterior T hT e s {O | bad (P (fullContext T hT e s)) O} ≤
        (m:ℝ≥0∞)*budget d r := by
  filter_upwards [TransportNetworkAuxiliary.edgePosterior_initialized (k := k) T hT e] with s hs
  apply finite_angle_failure (P (fullContext T hT e s)) d r hr (hardPairs T hT e s.1)
  · have hh := hardPairs_rank T hT e s.1; omega
  · exact hs.1
  · exact hs.2
  · exact hP _
  · exact hV s

theorem network_angle_failure {n D k m : ℕ} {β : Type*}
    (T : ℕ) (hT : T ≤ D) (e : Edge n) (d r : ℕ) (hr : 0<r) (hD : T+m+r≤D)
    (P : FullContext (D := D) e T k → Program D β m)
    (hP : ∀ c, Regular (P c))
    (hV : ∀ s : Sample n D k, Valid d (P (fullContext T hT e s)) (hardPairs T hT e s.1))
    (hmeas : MeasurableSet {p : FullContext (D := D) e T k × OrthogonalHaar.Group D |
      bad (P p.1) p.2}) :
    TransportNetworkAuxiliary.law n D k {s | bad (P (fullContext T hT e s)) (s.1.2 e)} ≤
      (m:ℝ≥0∞)*budget d r := by
  let μ := TransportNetworkAuxiliary.law n D k
  let o := fullContext (k := k) T hT e
  let b : FullContext (D := D) e T k → Sample n D k → Prop := fun c s => bad (P c) (s.1.2 e)
  have ho : Measurable o := fullContext_measurable T hT e
  have hmEdge : Measurable (fun s : Sample n D k => s.1.2 e) :=
    (measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)
  have hb : MeasurableSet {p : FullContext (D := D) e T k × Sample n D k | b p.1 p.2} :=
    (measurable_fst.prodMk (hmEdge.comp measurable_snd)) hmeas
  have ht : Measurable (fun c => condDistrib id o μ c {s | b c s}) :=
    Kernel.measurable_kernel_prodMk_left hb
  have hpost : ∀ᵐ c ∂μ.map o, condDistrib id o μ c {s | b c s} ≤ (m:ℝ≥0∞)*budget d r := by
    apply (ae_map_iff ho.aemeasurable (measurableSet_le ht measurable_const)).mpr
    filter_upwards [conditional_network_angle_failure T hT e d r hr hD P hP hV] with s hs
    have he : TransportNetworkAuxiliary.edgePosterior T hT e s {O | bad (P (o s)) O} =
        condDistrib id o μ (o s) {s' | b (o s) s'} :=
      Measure.map_apply hmEdge (bad_measurable (P (o s)) (hP _))
    rwa [← he]
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map ho.aemeasurable
  have he := ConditionalSupport.event_disintegration μ o ho _ hb
  change μ {s | b (o s) s} = ∫⁻ c, condDistrib id o μ c {s | b c s} ∂μ.map o at he
  change μ {s | b (o s) s} ≤ _
  rw [he]
  calc
    _ ≤ ∫⁻ _c, (m:ℝ≥0∞)*budget d r ∂μ.map o := lintegral_mono_ae hpost
    _ = _ := by simp

end Bilevel.TransportControllerEdge
