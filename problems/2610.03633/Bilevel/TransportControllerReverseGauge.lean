import Bilevel.TransportAuxiliaryContext
import Bilevel.TransportNetworkProjectionInformation

/-! The missing reverse-edge symmetry: a prefix gauge fixes the full
context but left-rotates the INVERSE current edge. Auxiliary orientations
remain fixed. This supplies the same actual paired-law theorem to reverse
innovations without asserting independence between the two directions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

def leftGauge {n D : ℕ} (e : Edge n) (z : Latent n D) (S : OrthogonalHaar.Group D) : Gauge n D :=
  fun v => if v.val ≤ e.val then relativeOrientation z v (src e)*S*(relativeOrientation z v (src e))⁻¹ else 1

theorem leftGauge_src {n D : ℕ} (e : Edge n) (z : Latent n D) (S : OrthogonalHaar.Group D) :
    leftGauge e z S (src e)=S := by simp [leftGauge,src,relativeOrientation]

theorem leftGauge_dst {n D : ℕ} (e : Edge n) (z : Latent n D) (S : OrthogonalHaar.Group D) :
    leftGauge e z S (dst e)=1 := by simp [leftGauge,dst]

theorem leftGauge_frame_fixed {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n)
    (z : Latent n D) (S : OrthogonalHaar.Group D)
    (hS : ∀ i, S • frame T hT z (src e) i = frame T hT z (src e) i)
    (v : Vertex n) (i : Fin T) : leftGauge e z S v • frame T hT z v i = frame T hT z v i := by
  by_cases h : v.val ≤ e.val
  · rw [leftGauge,if_pos h,← relative_frame T hT z v (src e) i]
    simp only [mul_smul,inv_smul_smul,hS]
  · simp only [leftGauge,if_neg h,one_smul]

theorem leftGauge_other_edge {n D : ℕ} (e f : Edge n) (hfe : f ≠ e)
    (z : Latent n D) (S : OrthogonalHaar.Group D) :
    leftGauge e z S (dst f)*z.2 f*(leftGauge e z S (src f))⁻¹ = z.2 f := by
  have hv : f.val ≠ e.val := fun h => hfe (Fin.ext h)
  by_cases h : f.val < e.val
  · have hdst : (dst f).val ≤ e.val := by simp only [dst,Fin.val_succ]; omega
    have hsrc : (src f).val ≤ e.val := by simp only [src,Fin.coe_castSucc]; omega
    rw [leftGauge,leftGauge,if_pos hdst,if_pos hsrc,relative_edge]
    group
  · have hdst : ¬(dst f).val ≤ e.val := by simp only [dst,Fin.val_succ]; omega
    have hsrc : ¬(src f).val ≤ e.val := by simp only [src,Fin.coe_castSucc]; omega
    simp only [leftGauge,if_neg hdst,if_neg hsrc,one_mul,inv_one,mul_one]

theorem leftGauge_context_fixed {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n)
    (z : Latent n D) (S : OrthogonalHaar.Group D)
    (hS : ∀ i, S • frame T hT z (src e) i = frame T hT z (src e) i) :
    leftGauge e z S • context T hT e z = context T hT e z := by
  apply Prod.ext
  · funext v i
    exact leftGauge_frame_fixed T hT e z S hS v i
  · funext f
    exact leftGauge_other_edge e f.val f.property z S

theorem leftGauge_inverse_edge_action {n D : ℕ} (e : Edge n) (z₀ z : Latent n D)
    (S : OrthogonalHaar.Group D) : ((gauge (leftGauge e z₀ S) z).2 e)⁻¹ = S*(z.2 e)⁻¹ := by
  change (leftGauge e z₀ S (dst e)*z.2 e*(leftGauge e z₀ S (src e))⁻¹)⁻¹ = _
  rw [leftGauge_dst,leftGauge_src,one_mul,mul_inv_rev,inv_inv]

def reverseHardPairs {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (z : Latent n D) :
    TransportEdgePosterior.Pairs D := List.ofFn (fun i : Fin T => (frame T hT z (dst e) i,frame T hT z (src e) i))

theorem reverseHardPairs_output_mem {n D : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n)
    (z : Latent n D) (i : Fin T) :
    frame T hT z (src e) i ∈ TransportEdgePosterior.range (reverseHardPairs T hT e z) :=
  pair_output_mem _ _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

end Bilevel.TransportNetwork

namespace Bilevel.TransportNetworkAuxiliary
open TransportNetwork EuclideanGaussian OrthogonalAction

def inverseEdgePosterior {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (s₀ : Sample n D k) :
    Measure (OrthogonalHaar.Group D) :=
  (condDistrib id (fullContext T hT e) (law n D k) (fullContext T hT e s₀)).map (fun s => (s.1.2 e)⁻¹)

instance inverseEdgePosterior_probability {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (s₀ : Sample n D k) :
    IsProbabilityMeasure (inverseEdgePosterior T hT e s₀) :=
  isProbabilityMeasure_map ((((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).inv).aemeasurable)

theorem inverseEdgePosterior_initialized {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) :
    ∀ᵐ s₀ ∂law n D k,
      TransportEdgePosterior.Invariant (TransportEdgePosterior.range (reverseHardPairs T hT e s₀.1))
        (inverseEdgePosterior T hT e s₀) ∧
      (∀ᵐ O ∂inverseEdgePosterior T hT e s₀, TransportEdgePosterior.Supports (reverseHardPairs T hT e s₀.1) O) := by
  have hp := ae_of_ae_map (fullContext_measurable (k := k) T hT e).aemeasurable
    (fullContext_posterior_isotropy (k := k) T hT e)
  have hf := ae_of_ae_map (fullContext_measurable (k := k) T hT e).aemeasurable
    (fullContext_network_fiber (k := k) T hT e)
  filter_upwards [hp,hf] with s₀ hs₀ hsFiber
  constructor
  · intro S
    let R := leftGauge e s₀.1 S.val
    have hfix : fullContextGauge R (fullContext T hT e s₀) = fullContext T hT e s₀ := by
      apply Prod.ext
      · apply leftGauge_context_fixed T hT e s₀.1 S.val
        intro i
        exact (ProjectionStabilizer.membership D (TransportEdgePosterior.range (reverseHardPairs T hT e s₀.1))
          S.val).mp S.property _ (reverseHardPairs_output_mem T hT e s₀.1 i)
      · rfl
    have hm : Measurable (fun s : Sample n D k => (s.1.2 e)⁻¹) :=
      ((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).inv
    apply ConditionalSymmetry.pushforward_preserving _ (fun s : Sample n D k => (s.1.2 e)⁻¹) hm
      (networkGauge R) (fun O : OrthogonalHaar.Group D => S.val*O) (hs₀ R hfix)
      (measurable_const.mul measurable_id)
    exact fun s => leftGauge_inverse_edge_action e s₀.1 s.1 S.val
  · apply (ae_map_iff ((((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).inv).aemeasurable)
      (TransportEdgePosterior.support_measurable (reverseHardPairs T hT e s₀.1))).mpr
    filter_upwards [hsFiber] with s hs
    apply (supports_iff_pairs _ _).mpr
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    have hsrc := congrArg (fun c : Context (d := D) e T => c.1 (src e) i) hs
    have hdst := congrArg (fun c : Context (d := D) e T => c.1 (dst e) i) hs
    change frame T hT s.1 (src e) i = frame T hT s₀.1 (src e) i at hsrc
    change frame T hT s.1 (dst e) i = frame T hT s₀.1 (dst e) i at hdst
    simpa only [hsrc,hdst] using reverse_edge_frame T hT s.1 e i

end Bilevel.TransportNetworkAuxiliary
