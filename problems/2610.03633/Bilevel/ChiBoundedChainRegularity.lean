import Bilevel.ChiBoundedChainProfileBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Dimension-independent regularity of the revised bounded chain

The proof uses the two coordinate supports of each edge. Constants come from
the actual scalar profiles; no chain Hessian bound is assumed.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ChiBoundedChain.Regularity
open ZeroChainPotential

theorem scalar_lip_of_deriv_bound (f : ℝ → ℝ) (K : ℝ)
    (hf : Differentiable ℝ f) (hb : ∀ x, |deriv f x| ≤ K) (x y : ℝ) :
    |f x - f y| ≤ K * |x - y| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ Set.univ) => hf z)
    (fun z (_ : z ∈ Set.univ) => by simpa only [Real.norm_eq_abs] using hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)

structure ProfileControl (K : ℝ) : Prop where
  nonnegative : 0 ≤ K
  psi0 : ∀ x, |psi x| ≤ K
  psi1 : ∀ x, |deriv psi x| ≤ K
  phi0 : ∀ x, |phi x| ≤ K
  phi1 : ∀ x, |deriv phi x| ≤ K
  psi0_lip : ∀ x y, |psi x - psi y| ≤ K * |x - y|
  psi1_lip : ∀ x y, |deriv psi x - deriv psi y| ≤ K * |x - y|
  phi0_lip : ∀ x y, |phi x - phi y| ≤ K * |x - y|
  phi1_lip : ∀ x y, |deriv phi x - deriv phi y| ≤ K * |x - y|

theorem psi_common_bound : ∃ A : ℝ, 0<A ∧
    ∀ j : Fin 4, ∀ t, |iteratedDeriv j.val psi t|≤A := by
  classical
  choose C hC hb using (fun j : Fin 4 => psi_jet_bound j.val (by omega))
  have hsum : 0≤∑ j,C j := Finset.sum_nonneg (fun j _ => hC j)
  refine ⟨1+∑ j,C j,by linarith,fun j t => ?_⟩
  have hh : C j≤∑ i,C i := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)
  exact (hb j t).trans (by linarith)

/-- All scalar controls are consequences of the revised bounded profile definitions. -/
theorem profile_control_exists : ∃ K : ℝ, ProfileControl K := by
  obtain ⟨A, hA, ha⟩ := psi_common_bound
  obtain ⟨B, hB, hb⟩ := phi_uniform_jet_bound
  have ha' (j : Fin 4) (x : ℝ) : |iteratedDeriv j.val psi x| ≤ A + B :=
    (ha j x).trans (le_add_of_nonneg_right hB.le)
  have hb' (j : Fin 4) (x : ℝ) : |iteratedDeriv j.val phi x| ≤ A + B :=
    (hb j x).trans (le_add_of_nonneg_left (by linarith))
  have p0 : ∀ x, |psi x| ≤ A + B := fun x => by simpa using ha' 0 x
  have p1 : ∀ x, |deriv psi x| ≤ A + B := fun x => by simpa only [Fin.val_one, iteratedDeriv_one] using ha' 1 x
  have p2 : ∀ x, |deriv (deriv psi) x| ≤ A + B := fun x => by
    have hh := ha' 2 x
    change |iteratedDeriv 2 psi x| ≤ A + B at hh
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] using hh
  have f0 : ∀ x, |phi x| ≤ A + B := fun x => by simpa using hb' 0 x
  have f1 : ∀ x, |deriv phi x| ≤ A + B := fun x => by simpa only [Fin.val_one, iteratedDeriv_one] using hb' 1 x
  have f2 : ∀ x, |deriv (deriv phi) x| ≤ A + B := fun x => by
    have hh := hb' 2 x
    change |iteratedDeriv 2 phi x| ≤ A + B at hh
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] using hh
  have pd : Differentiable ℝ (deriv psi) := by
    simpa only [iteratedDeriv_one] using (psi_contDiff (k := 2)).differentiable_iteratedDeriv 1 (by norm_num)
  have fd : Differentiable ℝ (deriv phi) := by
    simpa only [iteratedDeriv_one] using (phi_contDiff 2).differentiable_iteratedDeriv 1 (by norm_num)
  refine ⟨A + B, ⟨by linarith, p0, p1, f0, f1, ?_, ?_, ?_, ?_⟩⟩
  · exact scalar_lip_of_deriv_bound psi _ (fun x => (psi_hasDerivAt x).differentiableAt) p1
  · exact scalar_lip_of_deriv_bound (deriv psi) _ pd p2
  · exact scalar_lip_of_deriv_bound phi _ (fun x => (phi_hasDerivAt x).differentiableAt) f1
  · exact scalar_lip_of_deriv_bound (deriv phi) _ fd f2

theorem product_lip (f g : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ x, |f x| ≤ K) (hg : ∀ x, |g x| ≤ K)
    (hfl : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hgl : ∀ x y, |g x - g y| ≤ K * |x - y|) (a b c d : ℝ) :
    |f a * g b - f c * g d| ≤ K ^ 2 * (|a - c| + |b - d|) := by
  have he : f a * g b - f c * g d = (f a - f c) * g b + f c * (g b - g d) := by ring
  rw [he]
  have h0 : |(f a - f c) * g b| ≤ (K * |a - c|) * K := by
    rw [abs_mul]
    exact mul_le_mul (hfl a c) (hg b) (abs_nonneg _) (by positivity)
  have h1 : |f c * (g b - g d)| ≤ K * (K * |b - d|) := by
    rw [abs_mul]
    exact mul_le_mul (hf c) (hgl b d) (abs_nonneg _) hK
  exact (abs_add _ _).trans (by nlinarith)

theorem edgeLeft_lip {K : ℝ} (h : ProfileControl K) (a b c d : ℝ) :
    |edgeLeft a b - edgeLeft c d| ≤ 2 * K ^ 2 * (|a - c| + |b - d|) := by
  have hm := product_lip (deriv psi) phi K h.nonnegative h.psi1 h.phi0
    h.psi1_lip h.phi0_lip (-a) (-b) (-c) (-d)
  have hp := product_lip (deriv psi) phi K h.nonnegative h.psi1 h.phi0
    h.psi1_lip h.phi0_lip a b c d
  have he : edgeLeft a b - edgeLeft c d =
      -(deriv psi (-a) * phi (-b) - deriv psi (-c) * phi (-d)) -
        (deriv psi a * phi b - deriv psi c * phi d) := by unfold edgeLeft; ring
  rw [he]
  have ht := abs_sub (-(deriv psi (-a) * phi (-b) - deriv psi (-c) * phi (-d)))
    (deriv psi a * phi b - deriv psi c * phi d)
  rw [abs_neg] at ht
  simp only [neg_sub_neg, abs_sub_comm c a, abs_sub_comm d b] at hm
  linarith

theorem edgeRight_lip {K : ℝ} (h : ProfileControl K) (a b c d : ℝ) :
    |edgeRight a b - edgeRight c d| ≤ 2 * K ^ 2 * (|a - c| + |b - d|) := by
  have hm := product_lip psi (deriv phi) K h.nonnegative h.psi0 h.phi1
    h.psi0_lip h.phi1_lip (-a) (-b) (-c) (-d)
  have hp := product_lip psi (deriv phi) K h.nonnegative h.psi0 h.phi1
    h.psi0_lip h.phi1_lip a b c d
  have he : edgeRight a b - edgeRight c d =
      -(psi (-a) * deriv phi (-b) - psi (-c) * deriv phi (-d)) -
        (psi a * deriv phi b - psi c * deriv phi d) := by simp only [edgeRight, phi_deriv]; ring
  rw [he]
  have ht := abs_sub (-(psi (-a) * deriv phi (-b) - psi (-c) * deriv phi (-d)))
    (psi a * deriv phi b - psi c * deriv phi d)
  rw [abs_neg] at ht
  simp only [neg_sub_neg, abs_sub_comm c a, abs_sub_comm d b] at hm
  linarith

theorem norm_sum_basis_sq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Fin (n + 1)) (hf : Function.Injective f) (a : ι → ℝ) :
    ‖∑ i, a i • basis (f i)‖ ^ 2 = ∑ i, (a i) ^ 2 := by
  classical
  have hi (i j : ι) : ⟪basis (f i), basis (f j)⟫ = if i = j then (1 : ℝ) else 0 := by
    rw [inner_basis]
    simp [basis, hf.eq_iff]
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hi,
    mul_ite, mul_one, mul_zero]
  simp [pow_two]

theorem norm_sq_coordinates {n : ℕ} (d : Space n) : ‖d‖ ^ 2 = ∑ j, (d j) ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2
    (fun _ : Fin (n + 1) => ℝ) d

/-- The two shifted coordinate windows each occur only once in the Euclidean
sum of squares. This is where the chain length disappears. -/
theorem adjacent_squares_le {n : ℕ} (d : Space n) :
    (∑ i : Fin n, ((d i.castSucc) ^ 2 + (d i.succ) ^ 2)) ≤ 2 * ‖d‖ ^ 2 := by
  have hc : (∑ i : Fin n, (d i.castSucc) ^ 2) ≤ ‖d‖ ^ 2 := by
    rw [norm_sq_coordinates, Fin.sum_univ_castSucc]
    linarith [sq_nonneg (d (Fin.last n))]
  have hs : (∑ i : Fin n, (d i.succ) ^ 2) ≤ ‖d‖ ^ 2 := by
    rw [norm_sq_coordinates, Fin.sum_univ_succ]
    linarith [sq_nonneg (d 0)]
  rw [Finset.sum_add_distrib]
  linarith

theorem norm_sparse_coefficients_le {n : ℕ} (f : Fin n → Fin (n + 1))
    (hf : Function.Injective f) (a : Fin n → ℝ) (d : Space n) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M * (|d i.castSucc| + |d i.succ|)) :
    ‖∑ i, a i • basis (f i)‖ ≤ 2 * M * ‖d‖ := by
  have hi (i : Fin n) : (a i) ^ 2 ≤ 2 * M ^ 2 * ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) := by
    have hsq := (sq_le_sq₀ (abs_nonneg (a i))
      (show 0 ≤ M * (|d i.castSucc| + |d i.succ|) by positivity)).mpr (ha i)
    rw [sq_abs, mul_pow] at hsq
    have htwo : (|d i.castSucc| + |d i.succ|) ^ 2 ≤
        2 * ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) := by
      nlinarith [sq_abs (d i.castSucc), sq_abs (d i.succ),
        sq_nonneg (|d i.castSucc| - |d i.succ|)]
    have hh := mul_le_mul_of_nonneg_left htwo (sq_nonneg M)
    nlinarith
  have hs : ‖∑ i, a i • basis (f i)‖ ^ 2 ≤ (2 * M * ‖d‖) ^ 2 := by
    rw [norm_sum_basis_sq f hf]
    calc
      _ ≤ ∑ i : Fin n, 2 * M ^ 2 * ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = 2 * M ^ 2 * ∑ i : Fin n, ((d i.castSucc) ^ 2 + (d i.succ) ^ 2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * M ^ 2 * (2 * ‖d‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (adjacent_squares_le d) (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

theorem gradient_norm_sub_le {K : ℝ} (h : ProfileControl K) (n : ℕ) (x y : Space n) :
    ‖gradient (value n) x - gradient (value n) y‖ ≤ (K + 8 * K ^ 2) * ‖x - y‖ := by
  have hdecomp : gradientField n x - gradientField n y =
      ((-phiSlope (x 0)) - (-phiSlope (y 0))) • basis 0 +
      (∑ i : Fin n, (edgeLeft (x i.castSucc) (x i.succ) -
        edgeLeft (y i.castSucc) (y i.succ)) • basis i.castSucc) +
      (∑ i : Fin n, (edgeRight (x i.castSucc) (x i.succ) -
        edgeRight (y i.castSucc) (y i.succ)) • basis i.succ) := by
    simp only [gradientField, edgeGradient, Finset.sum_add_distrib, sub_smul, Finset.sum_sub_distrib]
    abel
  have hcoord : |x 0 - y 0| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) 0
  have hbase : ‖((-phiSlope (x 0)) - (-phiSlope (y 0))) • (basis 0 : Space n)‖ ≤ K * ‖x - y‖ := by
    calc
      _ = |deriv phi (x 0) - deriv phi (y 0)| := by
        simp only [norm_smul, basis, EuclideanSpace.norm_single, norm_one, mul_one,
          Real.norm_eq_abs, phi_deriv]
        rw [show -phiSlope (x 0) - -phiSlope (y 0) =
          -(phiSlope (x 0) - phiSlope (y 0)) by ring, abs_neg]
      _ ≤ K * |x 0 - y 0| := h.phi1_lip _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoord h.nonnegative
  have hl := norm_sparse_coefficients_le Fin.castSucc (Fin.castSucc_injective n)
    (fun i => edgeLeft (x i.castSucc) (x i.succ) - edgeLeft (y i.castSucc) (y i.succ))
    (x - y) (2 * K ^ 2) (by positivity) (fun i => edgeLeft_lip h _ _ _ _)
  have hr := norm_sparse_coefficients_le Fin.succ (Fin.succ_injective n)
    (fun i => edgeRight (x i.castSucc) (x i.succ) - edgeRight (y i.castSucc) (y i.succ))
    (x - y) (2 * K ^ 2) (by positivity) (fun i => edgeRight_lip h _ _ _ _)
  rw [actual_gradient, actual_gradient, hdecomp]
  have ht := (norm_add_le
    (((-phiSlope (x 0)) - (-phiSlope (y 0))) • (basis 0 : Space n) +
      ∑ i : Fin n, (edgeLeft (x i.castSucc) (x i.succ) - edgeLeft (y i.castSucc) (y i.succ)) • basis i.castSucc)
    (∑ i : Fin n, (edgeRight (x i.castSucc) (x i.succ) - edgeRight (y i.castSucc) (y i.succ)) • basis i.succ)).trans
      (add_le_add_right (norm_add_le _ _) _)
  nlinarith

/-- One numerical Lipschitz constant works for every chain dimension. -/
theorem gradient_lipschitz_uniform : ∃ L : NNReal, ∀ n : ℕ, LipschitzWith L (gradient (value n)) := by
  obtain ⟨K, hK⟩ := profile_control_exists
  refine ⟨⟨K + 8 * K ^ 2, by nlinarith [hK.nonnegative]⟩, fun n => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using gradient_norm_sub_le hK n x y

/-- The actual Hessian operator of the revised bounded chain is uniformly bounded,
independently of its length. -/
theorem gradient_contDiff (n k : ℕ) : ContDiff ℝ k (gradient (value n)) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.toContinuousLinearMap.contDiff.comp
    ((value_contDiff n (k + 1)).fderiv_right (by simp))

theorem gradient_hasFDerivAt (n : ℕ) (z : Space n) :
    HasFDerivAt (gradient (value n)) (fderiv ℝ (gradient (value n)) z) z :=
  ((gradient_contDiff n 1).differentiable (by norm_num) z).hasFDerivAt

theorem hessian_norm_uniform : ∃ L : NNReal, ∀ (n : ℕ) (z : Space n),
    ‖fderiv ℝ (gradient (value n)) z‖ ≤ L := by
  obtain ⟨L, hL⟩ := gradient_lipschitz_uniform
  exact ⟨L, fun n _ => norm_fderiv_le_of_lipschitz ℝ (hL n)⟩

end Bilevel.ChiBoundedChain.Regularity
