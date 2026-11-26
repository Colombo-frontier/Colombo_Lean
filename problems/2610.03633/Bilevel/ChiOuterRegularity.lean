import Bilevel.ChiOuterSize
import Bilevel.GradientJetBounds

/-! Dimension-independent Hessian bound for the actual one-sided bounded
macro chain, including the negative-side penalty. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiOuter.Regularity
open ChiBoundedChain ZeroChainPotential
open ChiBoundedChain.Regularity

theorem left_lip {K : ℝ} (h : ProfileControl K) (a b c d : ℝ) :
    |ChiOuter.edgeLeft a b-ChiOuter.edgeLeft c d|≤K^2*(|a-c|+|b-d|) := by
  have ht := product_lip (deriv psi) phi K h.nonnegative h.psi1 h.phi0
    h.psi1_lip h.phi0_lip a b c d
  simpa only [ChiOuter.edgeLeft,neg_mul,neg_sub_neg,abs_sub_comm] using ht

theorem right_lip {K : ℝ} (h : ProfileControl K) (a b c d : ℝ) :
    |ChiOuter.edgeRight a b-ChiOuter.edgeRight c d|≤K^2*(|a-c|+|b-d|) := by
  have ht := product_lip psi (deriv phi) K h.nonnegative h.psi0 h.phi1 h.psi0_lip h.phi1_lip a b c d
  simpa only [ChiOuter.edgeRight,phi_deriv,neg_mul,neg_sub_neg,abs_sub_comm] using ht

theorem theta_lipschitz_exists : ∃ T : ℝ,0≤T ∧ ∀ x y,|theta x-theta y|≤T*|x-y| := by
  obtain ⟨T,hT,hb⟩ := SmallGapProfileBounds.bound_of_compactSupport theta_deriv_compactSupport
    ((theta_contDiff (k:=2)).continuous_deriv (by norm_num))
  exact ⟨T,hT,scalar_lip_of_deriv_bound theta T ((theta_contDiff (k:=1)).differentiable (by norm_num)) hb⟩

theorem penalty_gradient_lip (T : ℝ) (hT : 0≤T) (ht : ∀ x y,|theta x-theta y|≤T*|x-y|)
    (n : ℕ) (x y : Space n) :
    ‖∑ i : Fin (n+1),(-theta (-x i)- -theta (-y i)) • basis i‖≤T*‖x-y‖ := by
  have hi (i : Fin (n+1)) : |(-theta (-x i)- -theta (-y i))|≤T*|(x-y) i| := by
    have hh := ht (-x i) (-y i)
    simpa only [neg_sub_neg,abs_sub_comm,PiLp.sub_apply] using hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (norm_nonneg _))).mp
  rw [ChiBoundedChain.Regularity.norm_sum_basis_sq (fun i : Fin (n+1) => i) Function.injective_id,mul_pow,norm_sq_coordinates,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤T*|(x-y) i|)).mpr (hi i)
  simpa only [mul_pow,sq_abs] using hs

theorem gradient_norm_sub_le {K T : ℝ} (h : ProfileControl K) (hT : 0≤T)
    (ht : ∀ x y,|theta x-theta y|≤T*|x-y|) (n : ℕ) (x y : Space n) :
    ‖gradient (ChiOuter.value n) x-gradient (ChiOuter.value n) y‖≤(K+4*K^2+T)*‖x-y‖ := by
  let a := (-phiSlope (x 0)- -phiSlope (y 0)) • (basis 0 : Space n)
  let l := ∑ i : Fin n,(ChiOuter.edgeLeft (x i.castSucc) (x i.succ)-ChiOuter.edgeLeft (y i.castSucc) (y i.succ)) • basis i.castSucc
  let r := ∑ i : Fin n,(ChiOuter.edgeRight (x i.castSucc) (x i.succ)-ChiOuter.edgeRight (y i.castSucc) (y i.succ)) • basis i.succ
  let p := ∑ i : Fin (n+1),(-theta (-x i)- -theta (-y i)) • basis i
  have he : gradient (ChiOuter.value n) x-gradient (ChiOuter.value n) y=a+l+r+p := by
    rw [ChiOuter.actual_gradient,ChiOuter.actual_gradient]
    dsimp only [a,l,r,p,ChiOuter.gradientField,ChiOuter.edgeGradient]
    simp only [Finset.sum_add_distrib,sub_smul,Finset.sum_sub_distrib]
    abel
  have hcoord : |x 0-y 0|≤‖x-y‖ := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) 0
  have ha : ‖a‖≤K*‖x-y‖ := by
    have hh := (h.phi1_lip (x 0) (y 0)).trans (mul_le_mul_of_nonneg_left hcoord h.nonnegative)
    simpa only [a,norm_smul,basis,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs,
      phi_deriv,neg_sub_neg,abs_sub_comm] using hh
  have hl : ‖l‖≤2*K^2*‖x-y‖ := norm_sparse_coefficients_le Fin.castSucc (Fin.castSucc_injective n)
    _ (x-y) (K^2) (sq_nonneg _) (fun i => left_lip h _ _ _ _)
  have hr : ‖r‖≤2*K^2*‖x-y‖ := norm_sparse_coefficients_le Fin.succ (Fin.succ_injective n)
    _ (x-y) (K^2) (sq_nonneg _) (fun i => right_lip h _ _ _ _)
  have hp : ‖p‖≤T*‖x-y‖ := penalty_gradient_lip T hT ht n x y
  rw [he]
  have h1 := norm_add_le (a+l+r) p
  have h2 := norm_add_le (a+l) r
  have h3 := norm_add_le a l
  nlinarith only [h1,h2,h3,ha,hl,hr,hp]

theorem gradient_lipschitz_uniform : ∃ L : NNReal,∀ n : ℕ,LipschitzWith L (gradient (ChiOuter.value n)) := by
  obtain ⟨K,hK⟩ := profile_control_exists
  obtain ⟨T,hT,ht⟩ := theta_lipschitz_exists
  refine ⟨⟨K+4*K^2+T,by nlinarith [hK.nonnegative]⟩,fun n => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using gradient_norm_sub_le hK hT ht n x y

theorem value_jet_two_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Space n),
    ‖iteratedFDeriv ℝ 2 (ChiOuter.value n) z‖≤C := by
  obtain ⟨L,hL⟩ := gradient_lipschitz_uniform
  refine ⟨L,L.coe_nonneg,fun n z => ?_⟩
  rw [← GradientJetBounds.hessian_norm_eq (ChiOuter.value_contDiff n 3) z]
  exact norm_fderiv_le_of_lipschitz ℝ (hL n)

theorem chain_jet_two_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ℓ h : ℝ),0≤ℓ → 0<h →
    ∀ z : Space n,‖iteratedFDeriv ℝ 2 (ChiOuter.chain n ℓ h) z‖≤C*ℓ := by
  obtain ⟨C,hC,hb⟩ := value_jet_two_uniform
  refine ⟨C,hC,fun n ℓ h hℓ hh z => ?_⟩
  have ht := ZeroChainResidualScaled.scaled_jet_bound (ChiOuter.value_contDiff n 3)
    (ℓ*h^2) h C (by positivity) hh 2 (by norm_num) (hb n) z
  change ‖iteratedFDeriv ℝ 2 (ChiOuter.chain n ℓ h) z‖≤C*(ℓ*h^2)/h^2 at ht
  convert ht using 1
  field_simp
  ring

end Bilevel.ChiOuter.Regularity
