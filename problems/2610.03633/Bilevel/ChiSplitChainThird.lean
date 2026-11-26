import Bilevel.ChiSplitChainRegularity
import Bilevel.ChiBoundedChainThird

/-! The actual split-chain Hessian has a dimension-independent Lipschitz
constant. The two endpoint coordinates of every edge remain separate. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ChiBoundedChain.Regularity ChiBoundedChain.Third ZeroChainPotential PrimitiveGeometry PartialLegendre

theorem split_left_derivative {n : ℕ} (i : Fin n) (z : Latent n) :
    HasFDerivAt (fun w : Latent n => edgeLeft (w.snd i.castSucc) (w.fst i.succ))
      (edgeLL (z.snd i.castSucc) (z.fst i.succ) • targetProjection i.castSucc+
        edgeLR (z.snd i.castSucc) (z.fst i.succ) • sourceProjection i.succ) z := by
  have hi := (targetProjection i.castSucc).hasFDerivAt (x:=z)
  have hj := (sourceProjection i.succ).hasFDerivAt (x:=z)
  have hm0 := (psi_deriv_hasDerivAt (-z.snd i.castSucc)).hasFDerivAt.comp z hi.neg
  have hm1 := (phi_hasDerivAt (-z.fst i.succ)).hasFDerivAt.comp z hj.neg
  have hp0 := (psi_deriv_hasDerivAt (z.snd i.castSucc)).hasFDerivAt.comp z hi
  have hp1 := (phi_hasDerivAt (z.fst i.succ)).hasFDerivAt.comp z hj
  convert (hm0.neg.mul hm1).sub (hp0.mul hp1) using 1
  ext v
  simp [edgeLL,edgeLR,ContinuousLinearMap.comp_apply,phi_deriv,sourceProjection_apply,targetProjection_apply]
  ring

theorem split_right_derivative {n : ℕ} (i : Fin n) (z : Latent n) :
    HasFDerivAt (fun w : Latent n => edgeRight (w.snd i.castSucc) (w.fst i.succ))
      (edgeLR (z.snd i.castSucc) (z.fst i.succ) • targetProjection i.castSucc+
        edgeRR (z.snd i.castSucc) (z.fst i.succ) • sourceProjection i.succ) z := by
  have hp (t : ℝ) : HasDerivAt psi (deriv psi t) t := by rw [psi_deriv]; exact psi_hasDerivAt t
  have hi := (targetProjection i.castSucc).hasFDerivAt (x:=z)
  have hj := (sourceProjection i.succ).hasFDerivAt (x:=z)
  have hm0 := (hp (-z.snd i.castSucc)).hasFDerivAt.comp z hi.neg
  have hm1 := (phi_deriv_hasDerivAt (-z.fst i.succ)).hasFDerivAt.comp z hj.neg
  have hp0 := (hp (z.snd i.castSucc)).hasFDerivAt.comp z hi
  have hp1 := (phi_deriv_hasDerivAt (z.fst i.succ)).hasFDerivAt.comp z hj
  convert (hm0.neg.mul hm1).sub (hp0.mul hp1) using 1
  · ext w
    simp [edgeRight,phi_deriv,sourceProjection_apply,targetProjection_apply]
  · ext v
    simp [edgeLR,edgeRR,ContinuousLinearMap.comp_apply,sourceProjection_apply,targetProjection_apply]
    ring

def sourceHessian (n : ℕ) (z : Latent n) : Latent n →L[ℝ] Space n :=
  ((-second phi (z.fst 0)) • sourceProjection 0).smulRight (basis 0)+
    ∑ i : Fin n,(edgeLR (z.snd i.castSucc) (z.fst i.succ) • targetProjection i.castSucc+
      edgeRR (z.snd i.castSucc) (z.fst i.succ) • sourceProjection i.succ).smulRight (basis i.succ)

def targetHessian (n : ℕ) (z : Latent n) : Latent n →L[ℝ] Space n :=
  ∑ i : Fin n,(edgeLL (z.snd i.castSucc) (z.fst i.succ) • targetProjection i.castSucc+
    edgeLR (z.snd i.castSucc) (z.fst i.succ) • sourceProjection i.succ).smulRight (basis i.castSucc)

def splitHessian (n : ℕ) (z : Latent n) : Latent n →L[ℝ] Latent n :=
  packLinear.comp ((sourceHessian n z).prod (targetHessian n z))

theorem source_gradient_derivative (n : ℕ) (z : Latent n) :
    HasFDerivAt (sourceGradient n) (sourceHessian n z) z := by
  have h0 := (((phi_deriv_hasDerivAt (z.fst 0)).hasFDerivAt.comp z
    (sourceProjection 0).hasFDerivAt).neg).smul_const (basis (0:Fin (n+1)))
  have hs := HasFDerivAt.sum (fun (i : Fin n) (_ : i∈Finset.univ) =>
    (split_right_derivative i z).smul_const (basis i.succ))
  convert h0.add hs using 1
  · ext w
    simp only [sourceGradient,Function.comp_apply,sourceProjection_apply,phi_deriv]
  · ext v
    simp [sourceHessian,ContinuousLinearMap.comp_apply,sourceProjection_apply,mul_comm]

theorem target_gradient_derivative (n : ℕ) (z : Latent n) :
    HasFDerivAt (targetGradient n) (targetHessian n z) z :=
  HasFDerivAt.sum (fun (i : Fin n) (_ : i∈Finset.univ) =>
    (split_left_derivative i z).smul_const (basis i.castSucc))

theorem actual_split_hessian (n : ℕ) (z : Latent n) :
    fderiv ℝ (gradient (value n)) z=splitHessian n z := by
  have hh := packLinear.hasFDerivAt.comp z
    ((source_gradient_derivative n z).prodMk (target_gradient_derivative n z))
  have he : (fun w => pack (sourceGradient n w) (targetGradient n w))=gradient (value n) := by
    funext w
    exact (actual_gradient n w).symm
  change HasFDerivAt (fun w => pack (sourceGradient n w) (targetGradient n w)) (splitHessian n z) z at hh
  rw [he] at hh
  exact hh.fderiv

theorem split_coordinate_bound {n : ℕ} (z : Latent n) (i : Fin (n+1)) :
    |z.fst i|≤‖z‖ ∧ |z.snd i|≤‖z‖ := by
  constructor
  · exact (show |z.fst i|≤‖z.fst‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.fst i).trans
      (WithLp.norm_fst_le (Space n) z)
  · exact (show |z.snd i|≤‖z.snd‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.snd i).trans
      (WithLp.norm_snd_le (Space n) z)

theorem split_pair_lip {K : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ a b c d,|f a b-f c d|≤2*K^2*(|a-c|+|b-d|))
    {n : ℕ} (x y : Latent n) (i : Fin n) :
    |f (x.snd i.castSucc) (x.fst i.succ)-f (y.snd i.castSucc) (y.fst i.succ)|≤4*K^2*‖x-y‖ := by
  have hc := (split_coordinate_bound (x-y) i.castSucc).2
  have hs := (split_coordinate_bound (x-y) i.succ).1
  change |x.snd i.castSucc-y.snd i.castSucc|≤‖x-y‖ at hc
  change |x.fst i.succ-y.fst i.succ|≤‖x-y‖ at hs
  have hc' := mul_le_mul_of_nonneg_left hc (sq_nonneg K)
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg K)
  exact (hf _ _ _ _).trans (by nlinarith only [hc',hs'])

theorem source_hessian_sub_apply (n : ℕ) (x y v : Latent n) :
    (sourceHessian n x-sourceHessian n y) v=
      ((-second phi (x.fst 0)+second phi (y.fst 0))*v.fst 0) • basis 0+
      ∑ i : Fin n,((edgeLR (x.snd i.castSucc) (x.fst i.succ)-edgeLR (y.snd i.castSucc) (y.fst i.succ))*v.snd i.castSucc+
        (edgeRR (x.snd i.castSucc) (x.fst i.succ)-edgeRR (y.snd i.castSucc) (y.fst i.succ))*v.fst i.succ) • basis i.succ := by
  simp only [sourceHessian,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,
    sourceProjection_apply,targetProjection_apply,smul_eq_mul]
  simp only [sub_mul,add_mul,add_smul,sub_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib,neg_mul,neg_smul]
  abel

theorem target_hessian_sub_apply (n : ℕ) (x y v : Latent n) :
    (targetHessian n x-targetHessian n y) v=
      ∑ i : Fin n,((edgeLL (x.snd i.castSucc) (x.fst i.succ)-edgeLL (y.snd i.castSucc) (y.fst i.succ))*v.snd i.castSucc+
        (edgeLR (x.snd i.castSucc) (x.fst i.succ)-edgeLR (y.snd i.castSucc) (y.fst i.succ))*v.fst i.succ) • basis i.castSucc := by
  simp only [targetHessian,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,
    sourceProjection_apply,targetProjection_apply,smul_eq_mul]
  simp only [sub_mul,add_mul,add_smul,sub_smul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem split_hessian_sub_apply_bound {K : ℝ} (h : ThirdControl K) (n : ℕ) (x y v : Latent n) :
    ‖(splitHessian n x-splitHessian n y) v‖≤(K+16*K^2)*‖x-y‖*‖v‖ := by
  have hcoord : |x.fst 0-y.fst 0|≤‖x-y‖ := (split_coordinate_bound (x-y) 0).1
  have hv := (split_coordinate_bound v 0).1
  have hbase : ‖((-second phi (x.fst 0)+second phi (y.fst 0))*v.fst 0) • (basis 0 : Space n)‖≤K*‖x-y‖*‖v‖ := by
    have hh : |-second phi (x.fst 0)+second phi (y.fst 0)|≤K*‖x-y‖ := by
      rw [show -second phi (x.fst 0)+second phi (y.fst 0)= -(second phi (x.fst 0)-second phi (y.fst 0)) by ring,abs_neg]
      exact (h.phi2_lip _ _).trans (mul_le_mul_of_nonneg_left hcoord h.nonnegative)
    simpa only [norm_smul,basis,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs,abs_mul] using
      mul_le_mul hh hv (abs_nonneg _) (mul_nonneg h.nonnegative (norm_nonneg _))
  have hr := norm_split_coefficients_le Fin.succ (Fin.succ_injective n)
    (fun i => (edgeLR (x.snd i.castSucc) (x.fst i.succ)-edgeLR (y.snd i.castSucc) (y.fst i.succ))*v.snd i.castSucc+
      (edgeRR (x.snd i.castSucc) (x.fst i.succ)-edgeRR (y.snd i.castSucc) (y.fst i.succ))*v.fst i.succ)
    v (4*K^2*‖x-y‖) (by positivity) (fun i => two_coefficients_bound _ _ _ _ _
      (split_pair_lip (edgeLR_lip h) x y i) (split_pair_lip (edgeRR_lip h) x y i))
  have hl := norm_split_coefficients_le Fin.castSucc (Fin.castSucc_injective n)
    (fun i => (edgeLL (x.snd i.castSucc) (x.fst i.succ)-edgeLL (y.snd i.castSucc) (y.fst i.succ))*v.snd i.castSucc+
      (edgeLR (x.snd i.castSucc) (x.fst i.succ)-edgeLR (y.snd i.castSucc) (y.fst i.succ))*v.fst i.succ)
    v (4*K^2*‖x-y‖) (by positivity) (fun i => two_coefficients_bound _ _ _ _ _
      (split_pair_lip (edgeLL_lip h) x y i) (split_pair_lip (edgeLR_lip h) x y i))
  change ‖pack ((sourceHessian n x-sourceHessian n y) v) ((targetHessian n x-targetHessian n y) v)‖≤_
  apply (latent_norm_le _ _).trans
  rw [source_hessian_sub_apply,target_hessian_sub_apply]
  exact (add_le_add_right (norm_add_le _ _) _).trans (by nlinarith only [hbase,hr,hl])

theorem split_hessian_lipschitz : ∃ C : NNReal,∀ n : ℕ,LipschitzWith C (fderiv ℝ (gradient (value n))) := by
  obtain ⟨K,hK⟩ := third_control_exists
  refine ⟨⟨K+16*K^2,by nlinarith only [hK.nonnegative,sq_nonneg K]⟩,fun n => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm,actual_split_hessian]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact split_hessian_sub_apply_bound hK n x y

theorem full_jet_three_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Latent n),
    ‖iteratedFDeriv ℝ 3 (value n) z‖≤C := by
  obtain ⟨C,hC⟩ := split_hessian_lipschitz
  refine ⟨C,C.coe_nonneg,fun n z => ?_⟩
  rw [← GradientJetBounds.third_norm_eq (value_contDiff n 3) z]
  exact norm_fderiv_le_of_lipschitz ℝ (hC n)

theorem chain_jet_three_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ell h : ℝ),
    0≤ell → 0<h → ∀ z : Latent n,‖iteratedFDeriv ℝ 3 (chain n ell h) z‖≤C*ell/h := by
  obtain ⟨C,hC,hb⟩ := full_jet_three_uniform
  refine ⟨C,hC,fun n ell h hell hh z => ?_⟩
  have ht := scaled_jet_bound (value_contDiff n 3) (ell*h^2) h C (by positivity) hh 3 (by norm_num) (hb n) z
  change ‖iteratedFDeriv ℝ 3 (chain n ell h) z‖≤_ at ht
  convert ht using 1
  field_simp
  ring

end Bilevel.ChiSplitChain
