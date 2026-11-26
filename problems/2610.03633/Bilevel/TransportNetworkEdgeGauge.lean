import Bilevel.TransportNetworkContext

/-! Edge-local residual rotations are realized by genuine layerwise gauges
that fix all full frames and all other edge maps. This proves residual left
isotropy of the actual current-edge conditional distribution. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

def relativeOrientation {n d : ℕ} (z : Latent n d) (v w : Vertex n) : OrthogonalHaar.Group d :=
  orientation z v.val*(orientation z w.val)⁻¹

def rightGauge {n d : ℕ} (e : Edge n) (z : Latent n d) (S : OrthogonalHaar.Group d) : Gauge n d :=
  fun v => if v.val ≤ e.val then 1 else
    relativeOrientation z v (dst e)*S*(relativeOrientation z v (dst e))⁻¹

theorem rightGauge_src {n d : ℕ} (e : Edge n) (z : Latent n d) (S : OrthogonalHaar.Group d) :
    rightGauge e z S (src e) = 1 := by simp [rightGauge,src]

theorem rightGauge_dst {n d : ℕ} (e : Edge n) (z : Latent n d) (S : OrthogonalHaar.Group d) :
    rightGauge e z S (dst e) = S := by simp [rightGauge,dst,relativeOrientation]

theorem relative_frame {n d : ℕ} (T : ℕ) (hT : T ≤ d) (z : Latent n d)
    (v w : Vertex n) (i : Fin T) :
    relativeOrientation z v w • frame T hT z w i = frame T hT z v i := by
  simp only [relativeOrientation,frame,mul_smul,inv_smul_smul]

theorem relative_edge {n d : ℕ} (z : Latent n d) (f : Edge n) (w : Vertex n) :
    relativeOrientation z (dst f) w = z.2 f*relativeOrientation z (src f) w := by
  simp only [relativeOrientation,src,dst,Fin.coe_castSucc,Fin.val_succ,orientation,dif_pos f.isLt,mul_assoc]

theorem rightGauge_frame_fixed {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n)
    (z : Latent n d) (S : OrthogonalHaar.Group d)
    (hS : ∀ i, S • frame T hT z (dst e) i = frame T hT z (dst e) i)
    (v : Vertex n) (i : Fin T) : rightGauge e z S v • frame T hT z v i = frame T hT z v i := by
  by_cases h : v.val ≤ e.val
  · simp only [rightGauge,if_pos h,one_smul]
  · rw [rightGauge,if_neg h,← relative_frame T hT z v (dst e) i]
    simp only [mul_smul,inv_smul_smul,hS]

theorem rightGauge_other_edge {n d : ℕ} (e f : Edge n) (hfe : f ≠ e)
    (z : Latent n d) (S : OrthogonalHaar.Group d) :
    rightGauge e z S (dst f)*z.2 f*(rightGauge e z S (src f))⁻¹ = z.2 f := by
  have hv : f.val ≠ e.val := fun h => hfe (Fin.ext h)
  by_cases h : f.val < e.val
  · have hdst : (dst f).val ≤ e.val := by simp only [dst,Fin.val_succ]; omega
    have hsrc : (src f).val ≤ e.val := by simp only [src,Fin.coe_castSucc]; omega
    simp only [rightGauge,if_pos hdst,if_pos hsrc,one_mul,inv_one,mul_one]
  · have hdst : ¬(dst f).val ≤ e.val := by simp only [dst,Fin.val_succ]; omega
    have hsrc : ¬(src f).val ≤ e.val := by simp only [src,Fin.coe_castSucc]; omega
    rw [rightGauge,rightGauge,if_neg hdst,if_neg hsrc,relative_edge]
    group

theorem rightGauge_context_fixed {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n)
    (z : Latent n d) (S : OrthogonalHaar.Group d)
    (hS : ∀ i, S • frame T hT z (dst e) i = frame T hT z (dst e) i) :
    rightGauge e z S • context T hT e z = context T hT e z := by
  apply Prod.ext
  · funext v i
    exact rightGauge_frame_fixed T hT e z S hS v i
  · funext f
    exact rightGauge_other_edge e f.val f.property z S

theorem rightGauge_edge_action {n d : ℕ} (e : Edge n) (z₀ z : Latent n d)
    (S : OrthogonalHaar.Group d) : (gauge (rightGauge e z₀ S) z).2 e = S*z.2 e := by
  change rightGauge e z₀ S (dst e)*z.2 e*(rightGauge e z₀ S (src e))⁻¹ = _
  rw [rightGauge_dst,rightGauge_src,inv_one,mul_one]

/-- The conditional edge law after observing full hard frames and all other
maps is left invariant under every rotation fixing its complete destination
frame. This is derived from the actual joint network prior. -/
theorem context_edge_posterior_left {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) :
    ∀ᵐ z₀ ∂law n d, ∀ S : OrthogonalHaar.Group d,
      (∀ i, S • frame T hT z₀ (dst e) i = frame T hT z₀ (dst e) i) →
      MeasurePreserving (fun O : OrthogonalHaar.Group d => S*O)
        ((condDistrib id (context T hT e) (law n d) (context T hT e z₀)).map (fun z => z.2 e))
        ((condDistrib id (context T hT e) (law n d) (context T hT e z₀)).map (fun z => z.2 e)) := by
  have hp := ae_of_ae_map (context_measurable T hT e).aemeasurable (context_posterior_isotropy T hT e)
  filter_upwards [hp] with z₀ hz₀
  intro S hS
  have hr := hz₀ (rightGauge e z₀ S) (rightGauge_context_fixed T hT e z₀ S hS)
  apply ConditionalSymmetry.pushforward_preserving _ (fun z : Latent n d => z.2 e)
    ((measurable_pi_apply e).comp measurable_snd)
    (gauge (rightGauge e z₀ S)) (fun O : OrthogonalHaar.Group d => S*O) hr
    (measurable_const.mul measurable_id)
  exact fun z => rightGauge_edge_action e z₀ z S

end Bilevel.TransportNetwork
