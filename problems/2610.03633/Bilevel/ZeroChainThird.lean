import Bilevel.ZeroChainRegularity

/-!
# Dimension-independent third-order control of the original zero chain

Actual Hessians are differentiated and estimated using their two-coordinate
edge supports. The scalar jet bounds are proved for the paper's profiles.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainThird
open ZeroChain ZeroChainProfiles ZeroChainPotential ZeroChainRegularity

def second (f : ℝ → ℝ) : ℝ → ℝ := deriv (deriv f)

theorem iteratedDeriv_two (f : ℝ → ℝ) : iteratedDeriv 2 f = second f := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rfl

theorem scalar_jet_lip (f : ℝ → ℝ) (K : ℝ) (hf : ContDiff ℝ 3 f)
    (hb : ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val f t| ≤ K)
    (k : ℕ) (hk : k < 3) (x y : ℝ) :
    |iteratedDeriv k f x - iteratedDeriv k f y| ≤ K * |x - y| := by
  apply scalar_lip_of_deriv_bound
  · exact hf.differentiable_iteratedDeriv k (by exact_mod_cast hk)
  · intro t
    rw [← iteratedDeriv_succ]
    exact hb ⟨k + 1, by omega⟩ t

structure ThirdControl (K : ℝ) : Prop extends ProfileControl K where
  psi2 : ∀ t, |second psi t| ≤ K
  phi2 : ∀ t, |second phi t| ≤ K
  psi2_lip : ∀ x y, |second psi x - second psi y| ≤ K * |x - y|
  phi2_lip : ∀ x y, |second phi x - second phi y| ≤ K * |x - y|

theorem third_control_exists : ∃ K : ℝ, ThirdControl K := by
  obtain ⟨A, hA, ha⟩ := psi_common_bound
  obtain ⟨B, hB, hb⟩ := phi_uniform_jet_bound
  have pa (j : Fin 4) (x : ℝ) : |iteratedDeriv j.val psi x| ≤ A + B :=
    (ha j x).trans (le_add_of_nonneg_right hB.le)
  have pb (j : Fin 4) (x : ℝ) : |iteratedDeriv j.val phi x| ≤ A + B :=
    (hb j x).trans (le_add_of_nonneg_left (by linarith))
  have lap (k : ℕ) (hk : k < 3) := scalar_jet_lip psi (A+B) (psi_contDiff (n:=3)) pa k hk
  have lbp (k : ℕ) (hk : k < 3) := scalar_jet_lip phi (A+B) (phi_contDiff 3) pb k hk
  have p2 (x : ℝ) : |second psi x| ≤ A+B := by
    have hh := pa 2 x
    change |iteratedDeriv 2 psi x| ≤ A+B at hh
    simpa only [iteratedDeriv_two] using hh
  have f2 (x : ℝ) : |second phi x| ≤ A+B := by
    have hh := pb 2 x
    change |iteratedDeriv 2 phi x| ≤ A+B at hh
    simpa only [iteratedDeriv_two] using hh
  refine ⟨A+B, ⟨⟨by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, p2, f2, ?_, ?_⟩⟩
  · simpa using pa 0
  · simpa only [Fin.val_one, iteratedDeriv_one] using pa 1
  · simpa using pb 0
  · simpa only [Fin.val_one, iteratedDeriv_one] using pb 1
  · simpa using lap 0 (by norm_num)
  · simpa only [iteratedDeriv_one] using lap 1 (by norm_num)
  · simpa using lbp 0 (by norm_num)
  · simpa only [iteratedDeriv_one] using lbp 1 (by norm_num)
  · simpa only [iteratedDeriv_two] using lap 2 (by norm_num)
  · simpa only [iteratedDeriv_two] using lbp 2 (by norm_num)

def edgeLL (a b : ℝ) : ℝ := second psi (-a) * phi (-b) - second psi a * phi b
def edgeLR (a b : ℝ) : ℝ := deriv psi (-a) * deriv phi (-b) - deriv psi a * deriv phi b
def edgeRR (a b : ℝ) : ℝ := psi (-a) * second phi (-b) - psi a * second phi b

theorem psi_deriv_hasDerivAt (t : ℝ) : HasDerivAt (deriv psi) (second psi t) t := by
  simpa only [iteratedDeriv_one, second] using
    ((psi_contDiff (n:=2)).differentiable_iteratedDeriv 1 (by norm_num) t).hasDerivAt

theorem phi_deriv_hasDerivAt (t : ℝ) : HasDerivAt (deriv phi) (second phi t) t := by
  simpa only [iteratedDeriv_one, second] using
    ((phi_contDiff 2).differentiable_iteratedDeriv 1 (by norm_num) t).hasDerivAt

theorem edgeLeft_hasFDerivAt {n : ℕ} (i : Fin n) (z : Space n) :
    HasFDerivAt (fun w : Space n => edgeLeft (w i.castSucc) (w i.succ))
      (edgeLL (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.castSucc +
        edgeLR (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.succ) z := by
  have hi := (EuclideanSpace.proj (𝕜:=ℝ) i.castSucc).hasFDerivAt (x:=z)
  have hj := (EuclideanSpace.proj (𝕜:=ℝ) i.succ).hasFDerivAt (x:=z)
  have hm0 := (psi_deriv_hasDerivAt (-z i.castSucc)).hasFDerivAt.comp z hi.neg
  have hm1 := (phi_hasDerivAt (-z i.succ)).hasFDerivAt.comp z hj.neg
  have hp0 := (psi_deriv_hasDerivAt (z i.castSucc)).hasFDerivAt.comp z hi
  have hp1 := (phi_hasDerivAt (z i.succ)).hasFDerivAt.comp z hj
  convert (hm0.neg.mul hm1).sub (hp0.mul hp1) using 1
  ext v
  simp [edgeLL, edgeLR, ContinuousLinearMap.comp_apply, phi_deriv]
  ring

theorem edgeRight_hasFDerivAt {n : ℕ} (i : Fin n) (z : Space n) :
    HasFDerivAt (fun w : Space n => edgeRight (w i.castSucc) (w i.succ))
      (edgeLR (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.castSucc +
        edgeRR (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.succ) z := by
  have hp (t : ℝ) : HasDerivAt psi (deriv psi t) t := by rw [psi_deriv]; exact psi_hasDerivAt t
  have hi := (EuclideanSpace.proj (𝕜:=ℝ) i.castSucc).hasFDerivAt (x:=z)
  have hj := (EuclideanSpace.proj (𝕜:=ℝ) i.succ).hasFDerivAt (x:=z)
  have hm0 := (hp (-z i.castSucc)).hasFDerivAt.comp z hi.neg
  have hm1 := (phi_deriv_hasDerivAt (-z i.succ)).hasFDerivAt.comp z hj.neg
  have hp0 := (hp (z i.castSucc)).hasFDerivAt.comp z hi
  have hp1 := (phi_deriv_hasDerivAt (z i.succ)).hasFDerivAt.comp z hj
  convert (hm0.neg.mul hm1).sub (hp0.mul hp1) using 1
  · ext w
    simp [edgeRight, phi_deriv]
  · ext v
    simp [edgeLR, edgeRR, ContinuousLinearMap.comp_apply]
    ring

def edgeHessian {n : ℕ} (i : Fin n) (z : Space n) : Space n →L[ℝ] Space n :=
  (edgeLL (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.castSucc +
    edgeLR (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.succ).smulRight (basis i.castSucc) +
  (edgeLR (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.castSucc +
    edgeRR (z i.castSucc) (z i.succ) • EuclideanSpace.proj (𝕜:=ℝ) i.succ).smulRight (basis i.succ)

def hessianField (n : ℕ) (z : Space n) : Space n →L[ℝ] Space n :=
  ((-second phi (z 0)) • EuclideanSpace.proj (𝕜:=ℝ) 0).smulRight (basis 0) +
    ∑ i : Fin n, edgeHessian i z

theorem edgeGradient_hasFDerivAt {n : ℕ} (i : Fin n) (z : Space n) :
    HasFDerivAt (edgeGradient i) (edgeHessian i z) z := by
  exact ((edgeLeft_hasFDerivAt i z).smul_const (basis i.castSucc)).add
    ((edgeRight_hasFDerivAt i z).smul_const (basis i.succ))

theorem actual_gradient_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (gradient (value n)) (hessianField n z) z := by
  have h0 := (((phi_deriv_hasDerivAt (z 0)).hasFDerivAt.comp z
    (EuclideanSpace.proj (𝕜:=ℝ) 0).hasFDerivAt).neg).smul_const (basis (0 : Fin (n+1)))
  have hs := HasFDerivAt.sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => edgeGradient_hasFDerivAt i z)
  convert h0.add hs using 1
  · ext w
    simp [actual_gradient, gradientField, phi_deriv]
  · ext v
    simp [hessianField, ContinuousLinearMap.comp_apply, mul_comm]

theorem actual_hessian (n : ℕ) (z : Space n) :
    fderiv ℝ (gradient (value n)) z = hessianField n z :=
  (actual_gradient_hasFDerivAt n z).fderiv

theorem edge_form_lip (f g : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ t, |f t| ≤ K) (hg : ∀ t, |g t| ≤ K)
    (hfl : ∀ x y, |f x-f y| ≤ K*|x-y|)
    (hgl : ∀ x y, |g x-g y| ≤ K*|x-y|) (a b c d : ℝ) :
    |(f (-a)*g (-b)-f a*g b) - (f (-c)*g (-d)-f c*g d)| ≤
      2*K^2*(|a-c|+|b-d|) := by
  have hm := product_lip f g K hK hf hg hfl hgl (-a) (-b) (-c) (-d)
  have hp := product_lip f g K hK hf hg hfl hgl a b c d
  simp only [neg_sub_neg, abs_sub_comm c a, abs_sub_comm d b] at hm
  have he : (f (-a)*g (-b)-f a*g b) - (f (-c)*g (-d)-f c*g d) =
    (f (-a)*g (-b)-f (-c)*g (-d)) - (f a*g b-f c*g d) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem edgeLL_lip {K : ℝ} (h : ThirdControl K) (a b c d : ℝ) :
    |edgeLL a b-edgeLL c d| ≤ 2*K^2*(|a-c|+|b-d|) :=
  edge_form_lip (second psi) phi K h.nonnegative h.psi2 h.phi0 h.psi2_lip h.phi0_lip a b c d

theorem edgeLR_lip {K : ℝ} (h : ThirdControl K) (a b c d : ℝ) :
    |edgeLR a b-edgeLR c d| ≤ 2*K^2*(|a-c|+|b-d|) :=
  edge_form_lip (deriv psi) (deriv phi) K h.nonnegative h.psi1 h.phi1 h.psi1_lip h.phi1_lip a b c d

theorem edgeRR_lip {K : ℝ} (h : ThirdControl K) (a b c d : ℝ) :
    |edgeRR a b-edgeRR c d| ≤ 2*K^2*(|a-c|+|b-d|) :=
  edge_form_lip psi (second phi) K h.nonnegative h.psi0 h.phi2 h.psi0_lip h.phi2_lip a b c d

theorem pair_lip_norm {K : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ a b c d, |f a b-f c d| ≤ 2*K^2*(|a-c|+|b-d|))
    {n : ℕ} (x y : Space n) (i : Fin n) :
    |f (x i.castSucc) (x i.succ)-f (y i.castSucc) (y i.succ)| ≤
      4*K^2*‖x-y‖ := by
  have hc : |x i.castSucc-y i.castSucc| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i.castSucc
  have hs : |x i.succ-y i.succ| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i.succ
  exact (hf _ _ _ _).trans (by nlinarith [sq_nonneg K])

theorem two_coefficients_bound (a b u v M : ℝ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a*u+b*v| ≤ M*(|u|+|v|) := by
  calc
    _ ≤ |a*u|+|b*v| := abs_add _ _
    _ ≤ M*|u|+M*|v| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
    _ = _ := by ring

theorem hessianField_apply (n : ℕ) (z v : Space n) :
    hessianField n z v = (-second phi (z 0)*v 0) • basis 0 +
      (∑ i : Fin n, (edgeLL (z i.castSucc) (z i.succ)*v i.castSucc +
        edgeLR (z i.castSucc) (z i.succ)*v i.succ) • basis i.castSucc) +
      (∑ i : Fin n, (edgeLR (z i.castSucc) (z i.succ)*v i.castSucc +
        edgeRR (z i.castSucc) (z i.succ)*v i.succ) • basis i.succ) := by
  simp [hessianField, edgeHessian, Finset.sum_add_distrib, add_assoc]

theorem hessian_sub_apply (n : ℕ) (x y v : Space n) :
    (hessianField n x-hessianField n y) v =
      ((-second phi (x 0)+second phi (y 0))*v 0) • basis 0 +
      (∑ i : Fin n, ((edgeLL (x i.castSucc) (x i.succ)-edgeLL (y i.castSucc) (y i.succ))*v i.castSucc +
        (edgeLR (x i.castSucc) (x i.succ)-edgeLR (y i.castSucc) (y i.succ))*v i.succ) • basis i.castSucc) +
      (∑ i : Fin n, ((edgeLR (x i.castSucc) (x i.succ)-edgeLR (y i.castSucc) (y i.succ))*v i.castSucc +
        (edgeRR (x i.castSucc) (x i.succ)-edgeRR (y i.castSucc) (y i.succ))*v i.succ) • basis i.succ) := by
  rw [ContinuousLinearMap.sub_apply, hessianField_apply, hessianField_apply]
  simp only [sub_mul, add_mul, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    neg_mul, neg_smul]
  abel

theorem hessian_sub_apply_norm_le {K : ℝ} (h : ThirdControl K) (n : ℕ) (x y v : Space n) :
    ‖(hessianField n x-hessianField n y) v‖ ≤ (K+16*K^2)*‖x-y‖*‖v‖ := by
  have hcoord (j : Fin (n+1)) : |x j-y j| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) j
  have hvcoord : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 0
  have hbase : ‖((-second phi (x 0)+second phi (y 0))*v 0) • (basis 0 : Space n)‖ ≤ K*‖x-y‖*‖v‖ := by
    have hscalar : |-second phi (x 0)+second phi (y 0)| ≤ K*‖x-y‖ := by
      rw [show -second phi (x 0)+second phi (y 0) = -(second phi (x 0)-second phi (y 0)) by ring, abs_neg]
      exact (h.phi2_lip _ _).trans (mul_le_mul_of_nonneg_left (hcoord 0) h.nonnegative)
    simpa only [norm_smul, basis, EuclideanSpace.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_mul] using mul_le_mul hscalar hvcoord (abs_nonneg (v 0))
        (mul_nonneg h.nonnegative (norm_nonneg _))
  have hl := norm_sparse_coefficients_le Fin.castSucc (Fin.castSucc_injective n)
    (fun i => (edgeLL (x i.castSucc) (x i.succ)-edgeLL (y i.castSucc) (y i.succ))*v i.castSucc +
      (edgeLR (x i.castSucc) (x i.succ)-edgeLR (y i.castSucc) (y i.succ))*v i.succ)
    v (4*K^2*‖x-y‖) (by positivity) (fun i => two_coefficients_bound _ _ _ _ _
      (pair_lip_norm (edgeLL_lip h) x y i) (pair_lip_norm (edgeLR_lip h) x y i))
  have hr := norm_sparse_coefficients_le Fin.succ (Fin.succ_injective n)
    (fun i => (edgeLR (x i.castSucc) (x i.succ)-edgeLR (y i.castSucc) (y i.succ))*v i.castSucc +
      (edgeRR (x i.castSucc) (x i.succ)-edgeRR (y i.castSucc) (y i.succ))*v i.succ)
    v (4*K^2*‖x-y‖) (by positivity) (fun i => two_coefficients_bound _ _ _ _ _
      (pair_lip_norm (edgeLR_lip h) x y i) (pair_lip_norm (edgeRR_lip h) x y i))
  rw [hessian_sub_apply]
  calc
    _ ≤ ‖((-second phi (x 0)+second phi (y 0))*v 0) • (basis 0 : Space n)‖ +
        ‖∑ i : Fin n, ((edgeLL (x i.castSucc) (x i.succ)-edgeLL (y i.castSucc) (y i.succ))*v i.castSucc +
          (edgeLR (x i.castSucc) (x i.succ)-edgeLR (y i.castSucc) (y i.succ))*v i.succ) • basis i.castSucc‖ +
        ‖∑ i : Fin n, ((edgeLR (x i.castSucc) (x i.succ)-edgeLR (y i.castSucc) (y i.succ))*v i.castSucc +
          (edgeRR (x i.castSucc) (x i.succ)-edgeRR (y i.castSucc) (y i.succ))*v i.succ) • basis i.succ‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ K*‖x-y‖*‖v‖ + 2*(4*K^2*‖x-y‖)*‖v‖ + 2*(4*K^2*‖x-y‖)*‖v‖ :=
      add_le_add (add_le_add hbase hl) hr
    _ = _ := by ring

theorem hessian_norm_sub_le {K : ℝ} (h : ThirdControl K) (n : ℕ) (x y : Space n) :
    ‖fderiv ℝ (gradient (value n)) x-fderiv ℝ (gradient (value n)) y‖ ≤
      (K+16*K^2)*‖x-y‖ := by
  rw [actual_hessian, actual_hessian]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by nlinarith [h.nonnegative]) (norm_nonneg _))
  exact hessian_sub_apply_norm_le h n x y

/-- A single Hessian Lipschitz constant works for all chain lengths. -/
theorem hessian_lipschitz_uniform : ∃ L : NNReal, ∀ n : ℕ,
    LipschitzWith L (fderiv ℝ (gradient (value n))) := by
  obtain ⟨K, hK⟩ := third_control_exists
  refine ⟨⟨K+16*K^2, by nlinarith [hK.nonnegative]⟩, fun n => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using hessian_norm_sub_le hK n x y

theorem hessian_contDiff (n k : ℕ) : ContDiff ℝ k (fderiv ℝ (gradient (value n))) :=
  (gradient_contDiff n (k+1)).fderiv_right (by simp)

theorem hessian_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (fderiv ℝ (gradient (value n)))
      (fderiv ℝ (fderiv ℝ (gradient (value n))) z) z :=
  ((hessian_contDiff n 1).differentiable (by norm_num) z).hasFDerivAt

/-- The actual derivative of the Hessian has a dimension-independent operator
norm bound. It represents the third differential through the real Riesz map. -/
theorem third_derivative_norm_uniform : ∃ L : NNReal, ∀ (n : ℕ) (z : Space n),
    ‖fderiv ℝ (fderiv ℝ (gradient (value n))) z‖ ≤ L := by
  obtain ⟨L, hL⟩ := hessian_lipschitz_uniform
  exact ⟨L, fun n _ => norm_fderiv_le_of_lipschitz ℝ (hL n)⟩

end Bilevel.ZeroChainThird
