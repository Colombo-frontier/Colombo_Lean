import Bilevel.ChiSplitChainLocality
import Bilevel.ChiSplitPayloadPrefix

/-! Both endpoint gradients of the actual centered split carrier retain
the old prefix. The source frontier cancellation uses the original split
formula off the response graph. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace Topology
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ZeroChainPotential PrimitiveGeometry

theorem frontier_target_gradient_support (n r : ℕ) (a b : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |b k|≤1/4) (k : Fin (n+1)) (hk : r≤k.val) :
    gradient (fun v => frontier n (pack a v)) b k=0 := by
  have hs (i : Fin (n+1)) := ((selector_hasFDerivAt n i b).neg).mul_const (phi (a i)-phi 0)
  have hd := HasFDerivAt.sum (u:=Finset.univ) (fun i _ => hs i)
  change HasFDerivAt (fun v => frontier n (pack a v)) _ b at hd
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hd,ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  change (phi (a i)-phi 0) • -((selectorDerivative n i b) (basis k))=0
  rw [selectorDerivative_basis_small i k b (hz k hk),neg_zero,smul_zero]

theorem carrier_target_gradient_support (n r : ℕ) (a b : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |b k|≤1/4) (k : Fin (n+1)) (hk : r≤k.val) :
    gradient (fun v => carrier n (pack a v)) b k=0 := by
  have hc : ContDiff ℝ 3 (fun v => value n (pack a v)) :=
    (value_contDiff n 3).comp ((packLinear (X:=Space n) (Y:=Space n)).contDiff.comp
      (contDiff_const.prodMk contDiff_id))
  have hf : ContDiff ℝ 3 (fun v => frontier n (pack a v)) :=
    (frontier_contDiff n 3).comp ((packLinear (X:=Space n) (Y:=Space n)).contDiff.comp
      (contDiff_const.prodMk contDiff_id))
  change gradient (fun v => value n (pack a v)-frontier n (pack a v)) b k=0
  rw [ChiFine.gradient_sub_C3 hc hf,(partial_y (value_hasGradientAt n (pack a b))).gradient]
  change targetGradient n (pack a b) k-gradient (fun v => frontier n (pack a v)) b k=0
  rw [targetGradient_support r (pack a b) hz k hk,frontier_target_gradient_support n r a b hz k hk,sub_self]

theorem carrier_gradient_support (n r : ℕ) (z : Latent n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z.snd k|≤1/4) :
    (∀ k : Fin (n+1),r≤k.val → (gradient (carrier n) z).fst k=0) ∧
    (∀ k : Fin (n+1),r≤k.val → (gradient (carrier n) z).snd k=0) := by
  have hf : ContDiff ℝ 3 (carrier n) := (value_contDiff n 3).sub (frontier_contDiff n 3)
  have hg := (hf.differentiable (by norm_num) z).hasGradientAt
  have hx : gradient (fun u => carrier n (pack u z.snd)) z.fst=(gradient (carrier n) z).fst :=
    (partial_x hg).gradient
  have hy : gradient (fun u => carrier n (pack z.fst u)) z.snd=(gradient (carrier n) z).snd :=
    (partial_y hg).gradient
  constructor
  · intro k hk
    rw [← hx]
    exact carrier_source_gradient_support r z.fst z.snd hz k hk
  · intro k hk
    rw [← hy]
    exact carrier_target_gradient_support n r z.fst z.snd hz k hk

end Bilevel.ChiSplitChain
