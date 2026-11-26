import Bilevel.ChiSplitFineData
import Bilevel.ChiSplitReadout
import Bilevel.ChiCarrierPrefixEvaluation

/-! Actual split fine scalar and first-jet retainSplit evaluation. Smallness is
required only in predecessor coordinates; the source profile is unrestricted. -/
noncomputable section
open scoped BigOperators Topology
namespace Bilevel.ChiSplitFine
open ChiBoundedChain PrimitiveGeometry PartialLegendre ChiPrefixEvaluation

def retainSplit (n r : ℕ) : Latent n →L[ℝ] Latent n :=
  ChiSplitChain.readout ((retain n (r+1)).comp jointFstLinear) ((retain n r).comp jointSndLinear)

theorem prefix_apply (n r : ℕ) (z : Latent n) :
    retainSplit n r z=pack (retain n (r+1) z.fst) (retain n r z.snd) := rfl

theorem selector_tail_zero {n : ℕ} (r : ℕ) (b : Space n)
    (hb : ∀ j : Fin (n+1),r≤j.val → |b j|≤1/4) (i : Fin (n+1)) (hi : r+1≤ i.val) :
    ChiBoundedChain.selector n i b=0 := by
  revert hi
  refine Fin.cases (by simp) (fun k hk => ?_) i
  have hs := hb k.castSucc (by change r≤k.val;simp only [Fin.val_succ] at hk;omega)
  simp only [ChiBoundedChain.selector,Fin.cases_succ,
    evenGate_zero (show |b k.castSucc|≤1/2 by linarith),zero_mul]

theorem selected_prefix_value {n : ℕ} (f : ℝ → ℝ) (r : ℕ) (z : Latent n)
    (hb : ∀ j : Fin (n+1),r≤j.val → |z.snd j|≤1/4) :
    selected n f z=selected n f (retainSplit n r z) := by
  have hsel (i : Fin (n+1)) : ChiBoundedChain.selector n i z.snd=
      ChiBoundedChain.selector n i (retain n r z.snd) := by
    simpa only [inv_one,one_smul] using selector_prefix_value n r 1 (by norm_num) i z.snd hb
  unfold selected term selector
  apply Finset.sum_congr rfl
  intro i _
  change ChiBoundedChain.selector n i z.snd*f (z.fst i)=
    ChiBoundedChain.selector n i (retain n r z.snd)*f (retain n (r+1) z.fst i)
  rw [← hsel i]
  by_cases hi : i.val<r+1
  · rw [retain_apply,if_pos hi]
  · rw [selector_tail_zero r z.snd hb i (by omega),zero_mul,zero_mul]

theorem selected_prefix_eventually {n : ℕ} (f : ℝ → ℝ) (r : ℕ) (z : Latent n)
    (hb : ∀ j : Fin (n+1),r≤j.val → |z.snd j|<1/4) :
    selected n f =ᶠ[𝓝 z] selected n f ∘ retainSplit n r := by
  have ho : IsOpen {w : Latent n | ∀ i : Fin (n+1),r≤ i.val → |w.snd i|<1/4} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp
      (jointSndLinear : Latent n →L[ℝ] Space n).continuous).abs) continuous_const
  filter_upwards [ho.mem_nhds hb] with w hw
  exact selected_prefix_value f r w (fun i hi => (hw i hi).le)

theorem selected_prefix_fderiv {n : ℕ} (f : ℝ → ℝ) (r : ℕ) (z : Latent n)
    (hb : ∀ j : Fin (n+1),r≤j.val → |z.snd j|<1/4) :
    fderiv ℝ (selected n f) z=fderiv ℝ (selected n f ∘ retainSplit n r) z :=
  (selected_prefix_eventually f r z hb).fderiv_eq

theorem selected_prefix_gradient {n : ℕ} (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f)
    (r : ℕ) (z : Latent n) (hb : ∀ j : Fin (n+1),r≤j.val → |z.snd j|<1/4) :
    gradient (selected n f) z=gradient (selected n f ∘ retainSplit n r) z := by
  have hg := (((selected_contDiff n hf).comp (retainSplit n r).contDiff).differentiable (by norm_num) z).hasGradientAt
  exact (hg.congr_of_eventuallyEq (selected_prefix_eventually f r z hb)).gradient

end Bilevel.ChiSplitFine
