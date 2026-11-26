import MatchingBounds1005.TensorSignals
import MatchingBounds1005.GaussianTensors
import MatchingBounds1005.GaussianFitter
import MatchingBounds1005.Confinement

/-! Actual normalized tensor channels, finite measurable Gaussian rows,
and exact value-gradient reconstruction. -/
noncomputable section
open scoped InnerProductSpace BigOperators ContDiff

namespace MatchingBounds1005.TensorGeometry

def channel {d : ℕ} (k : ℕ) (T : Tensor d k) (x : Vec d) : Vec d :=
  (k : ℝ)⁻¹ • gradient (polynomial T) x

theorem gradient_pairing {d : ℕ} (f : Vec d → ℝ) (x v : Vec d) :
    ⟪gradient f x, v⟫_ℝ = fderiv ℝ f x v := by
  change ((InnerProductSpace.toDual ℝ (Vec d))
    ((InnerProductSpace.toDual ℝ (Vec d)).symm (fderiv ℝ f x))) v = _
  rw [LinearIsometryEquiv.apply_symm_apply]

def channelRow {d : ℕ} (k : ℕ) (x : Vec d) (i : Fin d) : Tensor d k :=
  (k : ℝ)⁻¹ • gradientRow k x (EuclideanSpace.single i 1)

theorem channel_coordinate {d : ℕ} (k : ℕ) (T : Tensor d k) (x : Vec d) (i : Fin d) :
    channel k T x i = ⟪channelRow k x i, T⟫_ℝ := by
  have h := gradient_pairing (polynomial T) x (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at h
  simp only [channel, channelRow, PiLp.smul_apply, smul_eq_mul, real_inner_smul_left]
  rw [h, polynomial_fderiv_apply, real_inner_comm]

theorem channel_contraction {d k : ℕ} (hk : 1 ≤ k) (T : Tensor d k) (x : Vec d) :
    ⟪channel k T x, x⟫_ℝ = polynomial T x := by
  rw [channel, real_inner_smul_left, gradient_pairing]
  exact (polynomial_euler hk T x).symm

theorem channelRow_mem {d : ℕ} (k : ℕ) (W : Submodule ℝ (Vec d))
    {x : Vec d} (hx : x ∈ W) (i : Fin d) : channelRow k x i ∈ observationSpace k W :=
  (observationSpace k W).smul_mem _ (gradientRow_mem_observationSpace k W hx _)

theorem productTensor_continuous (d k : ℕ) : Continuous (@productTensor d k) := by
  apply (PiLp.continuous_equiv_symm 2 _).comp
  apply continuous_pi
  intro idx
  apply continuous_finset_prod
  intro j _
  exact (EuclideanSpace.proj (idx j)).continuous.comp (continuous_apply j)

theorem oneOutside_continuous {d k : ℕ} (v : Vec d) (i : Fin k) :
    Continuous (fun x : Vec d => oneOutside x v i) := by
  apply (productTensor_continuous d k).comp
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using (continuous_const : Continuous (fun _ : Vec d => v))
  · simpa only [Function.update_of_ne hj] using (continuous_id : Continuous (fun x : Vec d => x))

theorem channelRow_continuous {d : ℕ} (k : ℕ) (i : Fin d) :
    Continuous (fun x : Vec d => channelRow k x i) := by
  apply continuous_const.smul
  apply continuous_finset_sum
  intro j _
  exact oneOutside_continuous _ j

def channelCoordinates {d : ℕ} (k : ℕ) (x : Vec d) (i : Fin d) :
    Vec (Fintype.card (Fin k → Fin d)) := tensorCoordinates d k (channelRow k x i)

theorem channelCoordinates_measurable {d : ℕ} (k : ℕ) :
    Measurable (channelCoordinates (d := d) k) := by
  apply measurable_pi_lambda
  intro i
  exact ((tensorCoordinates d k).continuous.comp (channelRow_continuous k i)).measurable

theorem channelCoordinates_response {d : ℕ} (k : ℕ) (x : Vec d)
    (z : Vec (Fintype.card (Fin k → Fin d))) :
    GaussianFitter.rowResponse (channelCoordinates k x) z = fun i => channel k (gaussianTensor d k z) x i := by
  funext i
  rw [channel_coordinate]
  change ⟪tensorCoordinates d k (channelRow k x i), z⟫_ℝ = _
  rw [← (tensorCoordinates d k).inner_map_map]
  simp only [gaussianTensor, LinearIsometryEquiv.apply_symm_apply]

theorem mask_gradient_channels {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d) :
    gradient (mask T₃ T₄) x = channel 3 T₃ x + channel 4 T₄ x := by
  apply (InnerProductSpace.toDual ℝ (Vec d)).injective
  ext v
  have h3 := (polynomial_smooth T₃).differentiable (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  have h4 := (polynomial_smooth T₄).differentiable (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  change ⟪gradient (mask T₃ T₄) x, v⟫_ℝ = _
  rw [gradient_pairing]
  change fderiv ℝ (mask T₃ T₄) x v = ⟪channel 3 T₃ x + channel 4 T₄ x, v⟫_ℝ
  rw [inner_add_left, channel, channel, real_inner_smul_left, real_inner_smul_left,
    gradient_pairing, gradient_pairing]
  change fderiv ℝ (fun y => (1 / 3 : ℝ) * polynomial T₃ y + (1 / 4 : ℝ) * polynomial T₄ y) x v = _
  rw [fderiv_add (h3.const_mul (1 / 3 : ℝ)) (h4.const_mul (1 / 4 : ℝ)),
    fderiv_const_mul h3, fderiv_const_mul h4]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  norm_num

theorem mask_value_channels {d : ℕ} (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d) :
    mask T₃ T₄ x = ⟪channel 3 T₃ x, x⟫_ℝ / 3 + ⟪channel 4 T₄ x, x⟫_ℝ / 4 := by
  rw [channel_contraction (by omega : 1 ≤ 3), channel_contraction (by omega : 1 ≤ 4)]
  unfold mask
  ring

end MatchingBounds1005.TensorGeometry
