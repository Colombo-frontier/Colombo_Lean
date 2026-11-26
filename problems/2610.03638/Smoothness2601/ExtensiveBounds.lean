import Smoothness2601.ExtensiveChain
import Smoothness2601.SparseCoordinates

/-! Dimension-independent regularity of the actual extensive chain. Only
generic sparse-coordinate norm estimates are reused from the earlier chain;
all scalar estimates here concern the actual cutoff functions of 2601. -/
noncomputable section
namespace Smoothness2601.ExtensiveChain
open Cutoffs ChainProfiles Finset Filter Set
open SparseCoordinates
open scoped BigOperators RealInnerProductSpace Topology ContDiff

theorem psi_deriv_compact : HasCompactSupport (deriv psi) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2))
  intro t ht
  by_cases h : t < 1/2
  · exact psi_deriv_zero h
  · have hright : 1 < t := by
      by_contra hn
      exact ht ⟨by linarith, by linarith⟩
    have he : psi =ᶠ[𝓝 t] (fun _ => 1) := by
      exact (eventually_gt_nhds hright).mono fun u hu => psi_one hu.le
    simpa using he.deriv_eq

theorem psi_derivative_bounds : ∃ P Q : ℝ, 0 < P ∧ 0 < Q ∧
    (∀ t, |deriv psi t| ≤ P) ∧ (∀ t, |deriv (deriv psi) t| ≤ Q) := by
  have hd : ContDiff ℝ ∞ (deriv psi) := (contDiff_infty_iff_deriv.mp (psi_contDiff ⊤)).2
  obtain ⟨P,hP,hPb⟩ := compact_abs_bound psi_deriv_compact hd.continuous
  obtain ⟨Q,hQ,hQb⟩ := compact_abs_bound psi_deriv_compact.deriv
    (hd.continuous_deriv (by norm_num))
  exact ⟨P,Q,hP,hQ,hPb,hQb⟩

structure ActualProfileControl (M K : ℝ) : Prop where
  nonnegative : 0 ≤ K
  psi0 : ∀ x, |psi x| ≤ K
  psi1 : ∀ x, |deriv psi x| ≤ K
  phi0 : ∀ x, |profile M x| ≤ K
  phi1 : ∀ x, |deriv (profile M) x| ≤ K
  psi0_lip : ∀ x y, |psi x - psi y| ≤ K * |x - y|
  psi1_lip : ∀ x y, |deriv psi x - deriv psi y| ≤ K * |x - y|
  phi0_lip : ∀ x y, |profile M x - profile M y| ≤ K * |x - y|
  phi1_lip : ∀ x y, |deriv (profile M) x - deriv (profile M) y| ≤ K * |x - y|

theorem actual_profile_control_exists {M : ℝ} (hM : 0 ≤ M) : ∃ K : ℝ, ActualProfileControl M K := by
  obtain ⟨P,Q,hP,hQ,hPb,hQb⟩ := psi_derivative_bounds
  obtain ⟨Z,hZ,hZb⟩ := zeta_derivative_bound
  let K := 1 + P + Q + 4*M + M + M*Z
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have h1K : 1 ≤ K := by dsimp [K]; nlinarith [mul_nonneg hM hZ.le]
  have hPK : P ≤ K := by dsimp [K]; nlinarith [mul_nonneg hM hZ.le]
  have hQK : Q ≤ K := by dsimp [K]; nlinarith [mul_nonneg hM hZ.le]
  have h4MK : 4*M ≤ K := by dsimp [K]; nlinarith [mul_nonneg hM hZ.le]
  have hMK : M ≤ K := by dsimp [K]; nlinarith [mul_nonneg hM hZ.le]
  have hMZK : M*Z ≤ K := by dsimp [K]; nlinarith
  have hp0 : ∀ t, |psi t| ≤ K := fun t => by rw [abs_of_nonneg (psi_nonneg t)]; exact (psi_le_one t).trans h1K
  have hp1 : ∀ t, |deriv psi t| ≤ K := fun t => (hPb t).trans hPK
  have hp2 : ∀ t, |deriv (deriv psi) t| ≤ K := fun t => (hQb t).trans hQK
  have hf0 : ∀ t, |profile M t| ≤ K := fun t => by rw [abs_of_nonneg (profile_nonneg hM t)]; exact (profile_le_four_mul hM t).trans h4MK
  have hf1M : ∀ t, |deriv (profile M) t| ≤ M := by
    intro t
    rw [profile_deriv, abs_of_nonneg (mul_nonneg hM (zeta_nonneg t))]
    exact (mul_le_mul_of_nonneg_left (zeta_le_one t) hM).trans_eq (mul_one M)
  have hf1 : ∀ t, |deriv (profile M) t| ≤ K := fun t => (hf1M t).trans hMK
  have hpd : Differentiable ℝ (deriv psi) :=
    ((contDiff_infty_iff_deriv.mp (psi_contDiff ⊤)).2).differentiable (by norm_num)
  refine ⟨K,⟨hK,hp0,hp1,hf0,hf1,?_,?_,?_,?_⟩⟩
  · exact scalar_lip_of_deriv_bound psi K ((psi_contDiff 1).differentiable (by norm_num)) hp1
  · exact scalar_lip_of_deriv_bound (deriv psi) K hpd hp2
  · exact scalar_lip_of_deriv_bound (profile M) K (fun t => (profile_hasDerivAt M t).differentiableAt) hf1
  · intro x y
    have hz := scalar_lip_of_deriv_bound zeta Z ((zeta_contDiff 1).differentiable (by norm_num)) hZb x y
    rw [profile_deriv,profile_deriv,← mul_sub,abs_mul,abs_of_nonneg hM]
    calc
      _ ≤ M*(Z*|x-y|) := mul_le_mul_of_nonneg_left hz hM
      _ = (M*Z)*|x-y| := by ring
      _ ≤ K*|x-y| := mul_le_mul_of_nonneg_right hMZK (abs_nonneg _)

theorem leftSlope_lip {M K : ℝ} (h : ActualProfileControl M K) (a b c d : ℝ) :
    |leftSlope M a b-leftSlope M c d| ≤ 2*K^2*(|a-c|+|b-d|) := by
  have hm := product_lip (deriv psi) (profile M) K h.nonnegative h.psi1 h.phi0
    h.psi1_lip h.phi0_lip (-a) (-b) (-c) (-d)
  have hp := product_lip (deriv psi) (profile M) K h.nonnegative h.psi1 h.phi0
    h.psi1_lip h.phi0_lip a b c d
  have he : leftSlope M a b-leftSlope M c d =
      -(deriv psi (-a)*profile M (-b)-deriv psi (-c)*profile M (-d))-
      (deriv psi a*profile M b-deriv psi c*profile M d) := by unfold leftSlope; ring
  rw [he]
  have ht := abs_sub (-(deriv psi (-a)*profile M (-b)-deriv psi (-c)*profile M (-d)))
    (deriv psi a*profile M b-deriv psi c*profile M d)
  rw [abs_neg] at ht
  simp only [neg_sub_neg,abs_sub_comm c a,abs_sub_comm d b] at hm
  linarith

theorem rightSlope_lip {M K : ℝ} (h : ActualProfileControl M K) (a b c d : ℝ) :
    |rightSlope M a b-rightSlope M c d| ≤ 2*K^2*(|a-c|+|b-d|) := by
  have hm := product_lip psi (deriv (profile M)) K h.nonnegative h.psi0 h.phi1
    h.psi0_lip h.phi1_lip (-a) b (-c) d
  have hp := product_lip psi (deriv (profile M)) K h.nonnegative h.psi0 h.phi1
    h.psi0_lip h.phi1_lip a b c d
  have he : rightSlope M a b-rightSlope M c d =
      -(psi (-a)*deriv (profile M) b-psi (-c)*deriv (profile M) d)-
      (psi a*deriv (profile M) b-psi c*deriv (profile M) d) := by unfold rightSlope gate; ring
  rw [he]
  have ht := abs_sub (-(psi (-a)*deriv (profile M) b-psi (-c)*deriv (profile M) d))
    (psi a*deriv (profile M) b-psi c*deriv (profile M) d)
  rw [abs_neg] at ht
  simp only [neg_sub_neg,abs_sub_comm c a] at hm
  linarith

def gradientField (M : ℝ) {n : ℕ} (z : Space n) : Space n :=
  -deriv (profile M) (z 0) • SparseCoordinates.basis 0 +
  ∑ i : Fin n, (leftSlope M (z i.castSucc) (z i.succ) • SparseCoordinates.basis i.castSucc +
    rightSlope M (z i.castSucc) (z i.succ) • SparseCoordinates.basis i.succ)

theorem extensive_actual_gradient (M : ℝ) {n : ℕ} (z : Space n) :
    gradient (extensive M) z = gradientField M z := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert extensive_hasFDerivAt M z using 1
  ext v
  simp [InnerProductSpace.toDual_apply,gradientField,extensiveDerivative,linkDerivative,
    SparseCoordinates.basis,EuclideanSpace.inner_single_left,inner_sum]

theorem extensive_gradient_norm_sub_le {M K : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (x y : Space n) :
    ‖gradient (extensive M) x-gradient (extensive M) y‖ ≤ (K+8*K^2)*‖x-y‖ := by
  have hdecomp : gradientField M x-gradientField M y =
      ((-deriv (profile M) (x 0))-(-deriv (profile M) (y 0))) • SparseCoordinates.basis 0 +
      (∑ i : Fin n, (leftSlope M (x i.castSucc) (x i.succ)-
        leftSlope M (y i.castSucc) (y i.succ)) • SparseCoordinates.basis i.castSucc) +
      (∑ i : Fin n, (rightSlope M (x i.castSucc) (x i.succ)-
        rightSlope M (y i.castSucc) (y i.succ)) • SparseCoordinates.basis i.succ) := by
    simp only [gradientField,Finset.sum_add_distrib,sub_smul,Finset.sum_sub_distrib]
    abel
  have hcoord : |x 0-y 0| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) 0
  have hbase : ‖((-deriv (profile M) (x 0))-(-deriv (profile M) (y 0))) •
      (SparseCoordinates.basis 0 : Space n)‖ ≤ K*‖x-y‖ := by
    calc
      _ = |deriv (profile M) (x 0)-deriv (profile M) (y 0)| := by
        simp only [norm_smul,SparseCoordinates.basis,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs]
        rw [neg_sub_neg,abs_sub_comm]
      _ ≤ K*|x 0-y 0| := h.phi1_lip _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoord h.nonnegative
  have hl := norm_sparse_coefficients_le Fin.castSucc (Fin.castSucc_injective n)
    (fun i => leftSlope M (x i.castSucc) (x i.succ)-leftSlope M (y i.castSucc) (y i.succ))
    (x-y) (2*K^2) (by positivity) (fun i => leftSlope_lip h _ _ _ _)
  have hr := norm_sparse_coefficients_le Fin.succ (Fin.succ_injective n)
    (fun i => rightSlope M (x i.castSucc) (x i.succ)-rightSlope M (y i.castSucc) (y i.succ))
    (x-y) (2*K^2) (by positivity) (fun i => rightSlope_lip h _ _ _ _)
  rw [extensive_actual_gradient,extensive_actual_gradient,hdecomp]
  have ht := (norm_add_le
    (((-deriv (profile M) (x 0))-(-deriv (profile M) (y 0))) •
      (SparseCoordinates.basis 0 : Space n) +
      ∑ i : Fin n, (leftSlope M (x i.castSucc) (x i.succ)-leftSlope M (y i.castSucc) (y i.succ)) • SparseCoordinates.basis i.castSucc)
    (∑ i : Fin n, (rightSlope M (x i.castSucc) (x i.succ)-rightSlope M (y i.castSucc) (y i.succ)) • SparseCoordinates.basis i.succ)).trans
      (add_le_add_right (norm_add_le _ _) _)
  nlinarith

theorem extensive_gradient_lipschitz_uniform {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : NNReal, ∀ n : ℕ, LipschitzWith L (gradient (extensive M (n := n))) := by
  obtain ⟨K,hK⟩ := actual_profile_control_exists hM
  refine ⟨⟨K+8*K^2,by nlinarith [hK.nonnegative]⟩,fun n => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using extensive_gradient_norm_sub_le hK x y

theorem extensive_hessian_uniform {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : NNReal, ∀ (n : ℕ) (z : Space n), ‖fderiv ℝ (gradient (extensive M)) z‖ ≤ L := by
  obtain ⟨L,hL⟩ := extensive_gradient_lipschitz_uniform hM
  exact ⟨L,fun n _ => norm_fderiv_le_of_lipschitz ℝ (hL n)⟩

theorem leftSlope_abs_bound {M K : ℝ} (h : ActualProfileControl M K) (x y : ℝ) :
    |leftSlope M x y| ≤ 2*K^2 := by
  have h1 := mul_le_mul (h.psi1 (-x)) (h.phi0 (-y)) (abs_nonneg _) h.nonnegative
  have h2 := mul_le_mul (h.psi1 x) (h.phi0 y) (abs_nonneg _) h.nonnegative
  have ht := abs_sub (-deriv psi (-x)*profile M (-y)) (deriv psi x*profile M y)
  simp only [abs_mul,abs_neg] at ht
  unfold leftSlope
  nlinarith

theorem rightSlope_abs_bound {M K : ℝ} (h : ActualProfileControl M K) (x y : ℝ) :
    |rightSlope M x y| ≤ 2*K^2 := by
  have h1 := mul_le_mul (h.psi0 (-x)) (h.phi1 y) (abs_nonneg _) h.nonnegative
  have h2 := mul_le_mul (h.psi0 x) (h.phi1 y) (abs_nonneg _) h.nonnegative
  have he : rightSlope M x y = -(psi (-x)*deriv (profile M) y)-(psi x*deriv (profile M) y) := by
    unfold rightSlope gate; ring
  rw [he]
  have ht := abs_sub (-(psi (-x)*deriv (profile M) y)) (psi x*deriv (profile M) y)
  simp only [abs_mul,abs_neg] at ht
  nlinarith

theorem sparse_uniform_norm {n : ℕ} (f : Fin n → Fin (n+1)) (hf : Function.Injective f)
    (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) :
    ‖∑ i, a i • SparseCoordinates.basis (f i)‖ ≤ B*Real.sqrt (n+1) := by
  have hs : ‖∑ i, a i • SparseCoordinates.basis (f i)‖^2 ≤ n*B^2 := by
    rw [norm_sum_basis_sq f hf]
    calc
      _ ≤ ∑ _i : Fin n, B^2 := sum_le_sum fun i _ => by
        have hi := (sq_le_sq₀ (abs_nonneg _) hB).mpr (ha i)
        simpa only [sq_abs] using hi
      _ = _ := by simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ n+1)]
  nlinarith [sq_nonneg B]

theorem extensive_gradient_bound {M K : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (z : Space n) :
    ‖gradient (extensive M) z‖ ≤ (K+4*K^2)*Real.sqrt (n+1) := by
  have hroot : 1 ≤ Real.sqrt (n+1 : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
  have hb : ‖(-deriv (profile M) (z 0)) • (SparseCoordinates.basis 0 : Space n)‖ ≤ K*Real.sqrt (n+1) := by
    simp only [norm_smul,SparseCoordinates.basis,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs,abs_neg]
    exact (h.phi1 _).trans (le_mul_of_one_le_right h.nonnegative hroot)
  have hl := sparse_uniform_norm Fin.castSucc (Fin.castSucc_injective n)
    (fun i => leftSlope M (z i.castSucc) (z i.succ)) (by positivity : 0 ≤ 2*K^2)
    (fun i => leftSlope_abs_bound h _ _)
  have hr := sparse_uniform_norm Fin.succ (Fin.succ_injective n)
    (fun i => rightSlope M (z i.castSucc) (z i.succ)) (by positivity : 0 ≤ 2*K^2)
    (fun i => rightSlope_abs_bound h _ _)
  rw [extensive_actual_gradient,gradientField,sum_add_distrib]
  have ht := (norm_add_le
    ((-deriv (profile M) (z 0)) • (SparseCoordinates.basis 0 : Space n))
    ((∑ i : Fin n, leftSlope M (z i.castSucc) (z i.succ) • SparseCoordinates.basis i.castSucc)+
      ∑ i : Fin n, rightSlope M (z i.castSucc) (z i.succ) • SparseCoordinates.basis i.succ)).trans
    (add_le_add_left (norm_add_le _ _) _)
  nlinarith

theorem extensive_value_bound {M K : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (z : Space n) : |extensive M z| ≤ (K+2*K^2)*(n+1) := by
  have hedge (i : Fin n) : |link M (z i.castSucc) (z i.succ)| ≤ 2*K^2 := by
    have h1 := mul_le_mul (h.psi0 (-z i.castSucc)) (h.phi0 (-z i.succ)) (abs_nonneg _) h.nonnegative
    have h2 := mul_le_mul (h.psi0 (z i.castSucc)) (h.phi0 (z i.succ)) (abs_nonneg _) h.nonnegative
    have ht := abs_sub (psi (-z i.castSucc)*profile M (-z i.succ)) (psi (z i.castSucc)*profile M (z i.succ))
    simp only [abs_mul] at ht
    unfold link
    nlinarith
  have hs : |∑ i : Fin n, link M (z i.castSucc) (z i.succ)| ≤ n*(2*K^2) := by
    apply (abs_sum_le_sum_abs _ _).trans
    exact (sum_le_sum (fun i _ => hedge i)).trans_eq (by simp)
  have ht := abs_add (-profile M (z 0)) (∑ i : Fin n, link M (z i.castSucc) (z i.succ))
  rw [abs_neg] at ht
  have hp := h.phi0 (z 0)
  unfold extensive
  nlinarith [mul_nonneg h.nonnegative (Nat.cast_nonneg n),sq_nonneg K]

/-- All three extensive bounds, with constants independent of dimension. -/
theorem extensive_uniform_bounds {M : ℝ} (hM : 0 ≤ M) :
    ∃ CA CG CL : ℝ, 0 ≤ CA ∧ 0 ≤ CG ∧ 0 ≤ CL ∧ ∀ (n : ℕ) (z : Space n),
      |extensive M z| ≤ CA*(n+1) ∧
      ‖gradient (extensive M) z‖ ≤ CG*Real.sqrt (n+1) ∧
      ‖fderiv ℝ (gradient (extensive M)) z‖ ≤ CL := by
  obtain ⟨K,hK⟩ := actual_profile_control_exists hM
  obtain ⟨L,hL⟩ := extensive_hessian_uniform hM
  exact ⟨K+2*K^2,K+4*K^2,L,by nlinarith [hK.nonnegative],by nlinarith [hK.nonnegative],
    L.coe_nonneg,fun n z => ⟨extensive_value_bound hK z,extensive_gradient_bound hK z,hL n z⟩⟩

end Smoothness2601.ExtensiveChain
