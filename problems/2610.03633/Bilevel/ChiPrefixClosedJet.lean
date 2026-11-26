import Bilevel.ChiPrefixFrame
import Bilevel.GradientJetBounds

/-! Continuity extends prefix first-jet equality to the closed blind box.
No strict projection margin is needed at the inactive flattening boundary. -/
noncomputable section
open scoped Topology
open Filter Set
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain WrappedChain

theorem gradient_eq_retain_closed {n r s : ℕ} {τ : ℝ} (hτ : 0<τ) (f : Space n → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (z : Space n) (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤τ) :
    gradient f z=gradient f (retain n s z) := by
  have hc := (GradientJetBounds.gradient_contDiff hf).continuous
  have hclosed : IsClosed {w : Space n | gradient f w=gradient f (retain n s w)} :=
    isClosed_eq hc (hc.comp (retain n s).continuous)
  have ht : Tendsto (fun t : ℝ => t • z) (𝓝[<] (1:ℝ)) (𝓝 z) := by
    have hcont : Continuous (fun t : ℝ => t • z) := continuous_id.smul continuous_const
    simpa only [ContinuousWithinAt,one_smul] using (hcont.continuousAt (x:=1)).continuousWithinAt (s:=Iio 1)
  apply hclosed.mem_of_tendsto ht
  have hpos : ∀ᶠ t : ℝ in 𝓝[<] (1:ℝ),0<t :=
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,self_mem_nhdsWithin] with t ht0 ht1
  apply gradient_eq_retain hτ f (hf.differentiable (by norm_num)) hs
  intro k hk
  change |t*z k|<τ
  rw [abs_mul,abs_of_pos ht0]
  exact (mul_le_mul_of_nonneg_left (hz k hk) ht0.le).trans_lt (by
    have h := mul_lt_mul_of_pos_right ht1 hτ
    simpa only [one_mul] using h)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem wrapped_prefix_jet_closed {n r s : ℕ} {τ : ℝ} (hτ : 0<τ)
    (R : ℝ) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) (f : Space n → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hs : ∀ w : Space n,(∀ k : Fin (n+1),r≤k.val → |w k|≤τ) →
      ∀ k : Fin (n+1),s≤k.val → gradient f w k=0)
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n R U u k|≤τ) :
    f (coordinates n R U u)=prefixWrapped n s R U f u ∧
      gradient (f ∘ coordinates n R U) u=gradient (prefixWrapped n s R U f) u := by
  have hfd := hf.differentiable (by norm_num : (1:WithTop ℕ∞)≤3)
  refine ⟨value_eq_retain f hfd hs _ hu,?_⟩
  change gradient (f ∘ coordinates n R U) u=gradient ((f ∘ retain n s) ∘ coordinates n R U) u
  rw [WrappedPrefixLocality.carried_gradient n R hR U f hfd,
    WrappedPrefixLocality.carried_gradient n R hR U (f ∘ retain n s) (hfd.comp (retain n s).differentiable),
    gradient_comp_retain f hfd,←gradient_eq_retain_closed hτ f hf hs _ hu,
    retain_eq_of_tail_zero _ (hs _ hu)]

end Bilevel.ChiPrefixEvaluation
