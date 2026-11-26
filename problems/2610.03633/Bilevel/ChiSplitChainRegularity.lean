import Bilevel.ChiSplitChain
import Bilevel.ChiBoundedChainRegularity
import Bilevel.GradientJetBounds

/-! Dimension-independent actual split-chain Hessian. Each source and each
predecessor belongs to only one split edge; no transport-length factor enters. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ChiBoundedChain.Regularity ZeroChainPotential PrimitiveGeometry

theorem adjacent_squares_le {n : ℕ} (d : Latent n) :
    (∑ i : Fin n,((d.snd i.castSucc)^2+(d.fst i.succ)^2))≤2*‖d‖^2 := by
  have hc : (∑ i : Fin n,(d.snd i.castSucc)^2)≤‖d.snd‖^2 := by
    rw [norm_sq_coordinates,Fin.sum_univ_castSucc]
    linarith [sq_nonneg (d.snd (Fin.last n))]
  have hs : (∑ i : Fin n,(d.fst i.succ)^2)≤‖d.fst‖^2 := by
    rw [norm_sq_coordinates,Fin.sum_univ_succ]
    linarith [sq_nonneg (d.fst 0)]
  rw [Finset.sum_add_distrib,norm_sq]
  nlinarith only [hc,hs,sq_nonneg ‖d.fst‖,sq_nonneg ‖d.snd‖]

theorem norm_split_coefficients_le {n : ℕ} (f : Fin n → Fin (n+1))
    (hf : Function.Injective f) (a : Fin n → ℝ) (d : Latent n) (M : ℝ) (hM : 0≤M)
    (ha : ∀ i,|a i|≤M*(|d.snd i.castSucc|+|d.fst i.succ|)) :
    ‖∑ i,a i • basis (f i)‖≤2*M*‖d‖ := by
  have hi (i : Fin n) : (a i)^2≤2*M^2*((d.snd i.castSucc)^2+(d.fst i.succ)^2) := by
    have hsq := (sq_le_sq₀ (abs_nonneg (a i))
      (show 0≤M*(|d.snd i.castSucc|+|d.fst i.succ|) by positivity)).mpr (ha i)
    rw [sq_abs,mul_pow] at hsq
    have htwo : (|d.snd i.castSucc|+|d.fst i.succ|)^2≤
        2*((d.snd i.castSucc)^2+(d.fst i.succ)^2) := by
      nlinarith [sq_abs (d.snd i.castSucc),sq_abs (d.fst i.succ),
        sq_nonneg (|d.snd i.castSucc|-|d.fst i.succ|)]
    have hh := mul_le_mul_of_nonneg_left htwo (sq_nonneg M)
    nlinarith only [hsq,hh]
  have hs : ‖∑ i,a i • basis (f i)‖^2≤(2*M*‖d‖)^2 := by
    rw [norm_sum_basis_sq f hf]
    calc
      _≤∑ i : Fin n,2*M^2*((d.snd i.castSucc)^2+(d.fst i.succ)^2) := Finset.sum_le_sum (fun i _ => hi i)
      _=2*M^2*∑ i : Fin n,((d.snd i.castSucc)^2+(d.fst i.succ)^2) := (Finset.mul_sum _ _ _).symm
      _≤2*M^2*(2*‖d‖^2) := mul_le_mul_of_nonneg_left (adjacent_squares_le d) (by positivity)
      _=_ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

theorem latent_norm_le {n : ℕ} (a b : Space n) : ‖pack a b‖≤‖a‖+‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sq]
  change ‖a‖^2+‖b‖^2≤(‖a‖+‖b‖)^2
  nlinarith [norm_nonneg a,norm_nonneg b]

theorem gradient_norm_sub_le {K : ℝ} (h : ProfileControl K) (n : ℕ) (x y : Latent n) :
    ‖gradient (value n) x-gradient (value n) y‖≤(K+8*K^2)*‖x-y‖ := by
  have hsource : sourceGradient n x-sourceGradient n y=
      ((-phiSlope (x.fst 0))-(-phiSlope (y.fst 0))) • basis 0+
        ∑ i : Fin n,(edgeRight (x.snd i.castSucc) (x.fst i.succ)-
          edgeRight (y.snd i.castSucc) (y.fst i.succ)) • basis i.succ := by
    simp only [sourceGradient,sub_smul,Finset.sum_sub_distrib]
    abel
  have htarget : targetGradient n x-targetGradient n y=
      ∑ i : Fin n,(edgeLeft (x.snd i.castSucc) (x.fst i.succ)-
        edgeLeft (y.snd i.castSucc) (y.fst i.succ)) • basis i.castSucc := by
    simp only [targetGradient,sub_smul,Finset.sum_sub_distrib]
  have hcoord : |x.fst 0-y.fst 0|≤‖x-y‖ := by
    have hh : |x.fst 0-y.fst 0|≤‖x.fst-y.fst‖ := by
      simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x.fst-y.fst) 0
    exact hh.trans (WithLp.norm_fst_le (Space n) (x-y))
  have hbase : ‖((-phiSlope (x.fst 0))-(-phiSlope (y.fst 0))) • (basis 0 : Space n)‖≤K*‖x-y‖ := by
    calc
      _=|deriv phi (x.fst 0)-deriv phi (y.fst 0)| := by
        simp only [norm_smul,basis,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs,phi_deriv]
        rw [show -phiSlope (x.fst 0)- -phiSlope (y.fst 0)=
          -(phiSlope (x.fst 0)-phiSlope (y.fst 0)) by ring,abs_neg]
      _≤K*|x.fst 0-y.fst 0| := h.phi1_lip _ _
      _≤_ := mul_le_mul_of_nonneg_left hcoord h.nonnegative
  have hl := norm_split_coefficients_le Fin.castSucc (Fin.castSucc_injective n)
    (fun i => edgeLeft (x.snd i.castSucc) (x.fst i.succ)-edgeLeft (y.snd i.castSucc) (y.fst i.succ))
    (x-y) (2*K^2) (by positivity) (fun i => edgeLeft_lip h _ _ _ _)
  have hr := norm_split_coefficients_le Fin.succ (Fin.succ_injective n)
    (fun i => edgeRight (x.snd i.castSucc) (x.fst i.succ)-edgeRight (y.snd i.castSucc) (y.fst i.succ))
    (x-y) (2*K^2) (by positivity) (fun i => edgeRight_lip h _ _ _ _)
  rw [actual_gradient,actual_gradient]
  change ‖pack (sourceGradient n x-sourceGradient n y) (targetGradient n x-targetGradient n y)‖≤_
  apply (latent_norm_le _ _).trans
  rw [hsource,htarget]
  have hh := norm_add_le (((-phiSlope (x.fst 0))-(-phiSlope (y.fst 0))) • (basis 0 : Space n))
    (∑ i : Fin n,(edgeRight (x.snd i.castSucc) (x.fst i.succ)-edgeRight (y.snd i.castSucc) (y.fst i.succ)) • basis i.succ)
  nlinarith only [hh,hl,hr,hbase]

theorem gradient_lipschitz_uniform : ∃ L : NNReal,∀ n : ℕ,LipschitzWith L (gradient (value n)) := by
  obtain ⟨K,hK⟩ := profile_control_exists
  refine ⟨⟨K+8*K^2,by nlinarith [hK.nonnegative]⟩,fun n => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using gradient_norm_sub_le hK n x y

theorem full_jet_two_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Latent n),
    ‖iteratedFDeriv ℝ 2 (value n) z‖≤C := by
  obtain ⟨L,hL⟩ := gradient_lipschitz_uniform
  refine ⟨L,L.coe_nonneg,fun n z => ?_⟩
  rw [← GradientJetBounds.hessian_norm_eq (value_contDiff n 3) z]
  exact norm_fderiv_le_of_lipschitz ℝ (hL n)

theorem scaled_jet_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ 3 f) (a β B : ℝ) (ha : 0≤a) (hβ : 0<β)
    (k : ℕ) (hk : k≤3) (hb : ∀ z,‖iteratedFDeriv ℝ k f z‖≤B) (z : X) :
    ‖iteratedFDeriv ℝ k (fun w => a*f (β⁻¹ • w)) z‖≤B*a/β^k := by
  let g : X →L[ℝ] X := β⁻¹ • ContinuousLinearMap.id ℝ X
  have hg : ‖g‖≤β⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound g (inv_nonneg.mpr hβ.le)
    intro w
    change ‖β⁻¹ • w‖≤β⁻¹*‖w‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hβ)]
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  change ‖iteratedFDeriv ℝ k (fun w => a • (f ∘ g) w) z‖≤_
  rw [iteratedFDeriv_const_smul_apply' ((hf.comp g.contDiff).of_le hk').contDiffAt,
    norm_smul a (iteratedFDeriv ℝ k (f ∘ g) z),Real.norm_eq_abs,abs_of_nonneg ha,
    g.iteratedFDeriv_comp_right hf z hk']
  have hc := ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ k f (g z)) (fun _ => g)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hc
  have hc' := hc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg g) hg k)
    (norm_nonneg (iteratedFDeriv ℝ k f (g z))))
  calc
    _≤a*(‖iteratedFDeriv ℝ k f (g z)‖*(β⁻¹)^k) := mul_le_mul_of_nonneg_left hc' ha
    _≤a*(B*(β⁻¹)^k) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hb _) (by positivity)) ha
    _=B*a/β^k := by rw [inv_pow,div_eq_mul_inv]; ring

theorem chain_jet_two_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ell h : ℝ),
    0≤ell → 0<h → ∀ z : Latent n,‖iteratedFDeriv ℝ 2 (chain n ell h) z‖≤C*ell := by
  obtain ⟨C,hC,hb⟩ := full_jet_two_uniform
  refine ⟨C,hC,fun n ell h hell hh z => ?_⟩
  have ht := scaled_jet_bound (value_contDiff n 3)
    (ell*h^2) h C (by positivity) hh 2 (by norm_num) (hb n) z
  change ‖iteratedFDeriv ℝ 2 (chain n ell h) z‖≤C*(ell*h^2)/h^2 at ht
  convert ht using 1
  field_simp
  ring

end Bilevel.ChiSplitChain
