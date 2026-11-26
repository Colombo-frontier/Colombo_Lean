import MatchingBounds1005.TensorOracle
import MatchingBounds1005.Model
import MatchingBounds1005.SymmetricQuadratic
import MatchingBounds1005.OracleMeasurability

/-! Exact value-gradient oracle reconstruction from simultaneous normalized
tensor channels and disclosed taper corrections. -/
noncomputable section
open scoped InnerProductSpace BigOperators ContDiff

namespace MatchingBounds1005.TensorGeometry

theorem mask_add {d : ℕ} (S₃ T₃ : Tensor d 3) (S₄ T₄ : Tensor d 4) (x : Vec d) :
    mask (S₃ + T₃) (S₄ + T₄) x = mask S₃ S₄ x + mask T₃ T₄ x := by
  simp only [mask, polynomial_add]
  ring

def correctionSum {ι : Type*} {d : ℕ} (b : ι → Vec d) (τ r A : ℝ)
    (S : Finset ι) (x : Vec d) : ℝ := τ * ∑ i ∈ S, Primitive.correction r (A * ⟪b i, x⟫_ℝ)

theorem correctionSum_smooth {ι : Type*} {d : ℕ} (b : ι → Vec d) (τ r A : ℝ)
    (S : Finset ι) : ContDiff ℝ ∞ (correctionSum b τ r A S) := by
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  exact (Primitive.correction_smooth r).comp
    (contDiff_const.mul (contDiff_const.inner ℝ contDiff_id))

theorem correctionSum_joint_continuous {ι : Type*} {d : ℕ} (τ r A : ℝ) (S : Finset ι) :
    Continuous (fun z : (ι → Vec d) × Vec d => correctionSum z.1 τ r A S z.2) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i _
  exact (Primitive.correction_smooth r).continuous.comp
    (continuous_const.mul (((continuous_apply i).comp continuous_fst).inner continuous_snd))

theorem correctionSum_oracle_measurable {ι : Type*} [Fintype ι] {d : ℕ}
    (τ r A : ℝ) (S : Finset ι) :
    Measurable (fun z : (ι → Vec d) × Vec d => Model.oracle (correctionSum z.1 τ r A S) z.2) :=
  Model.oracle_measurable_of_continuous
    (F := fun b : ι → Vec d => correctionSum b τ r A S)
    (correctionSum_joint_continuous τ r A S)

def ridgeMasked {ι : Type*} [Fintype ι] {d : ℕ} (Q : Vec d → ℝ)
    (b : ι → Vec d) (τ r A : ℝ) (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d) : ℝ :=
  Q x + τ * ridgeSum b (Primitive.potential r) A x + mask T₃ T₄ x

def disclosedMasked {ι : Type*} [Fintype ι] {d : ℕ} (Q : Vec d → ℝ)
    (b : ι → Vec d) (τ r A : ℝ) (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (S : Finset ι) (x : Vec d) : ℝ :=
  Q x + (mask (cubicSignal τ A b + T₃) (quarticSignal τ A b + T₄) x +
    10 * τ * Fintype.card ι) + correctionSum b τ r A S x

theorem ridgeMasked_smooth {ι : Type*} [Fintype ι] {d : ℕ} {Q : Vec d → ℝ}
    (hQ : ContDiff ℝ ∞ Q) (b : ι → Vec d) (τ r A : ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) : ContDiff ℝ ∞ (ridgeMasked Q b τ r A T₃ T₄) :=
  (hQ.add (contDiff_const.mul (ridgeSum_smooth b (Primitive.potential_smooth r) A))).add
    (mask_smooth T₃ T₄)

theorem disclosedMasked_smooth {ι : Type*} [Fintype ι] {d : ℕ} {Q : Vec d → ℝ}
    (hQ : ContDiff ℝ ∞ Q) (b : ι → Vec d) (τ r A : ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) (S : Finset ι) :
    ContDiff ℝ ∞ (disclosedMasked Q b τ r A T₃ T₄ S) :=
  (hQ.add ((mask_smooth _ _).add contDiff_const)).add (correctionSum_smooth b τ r A S)

theorem ridgeMasked_eq_full_disclosure {ι : Type*} [Fintype ι] {d : ℕ}
    (Q : Vec d → ℝ) (b : ι → Vec d) (τ r A : ℝ) (T₃ : Tensor d 3) (T₄ : Tensor d 4) :
    ridgeMasked Q b τ r A T₃ T₄ = disclosedMasked Q b τ r A T₃ T₄ Finset.univ := by
  funext x
  unfold ridgeMasked disclosedMasked correctionSum
  rw [potential_tensor_decomposition, mask_add]
  unfold ridgeSum
  ring

theorem disclosed_oracle_exact {ι : Type*} [Fintype ι] {d : ℕ} {Q : Vec d → ℝ}
    (hQ : ContDiff ℝ ∞ Q) (b : ι → Vec d) (τ A : ℝ) {r : ℝ} (hr : 1 ≤ r)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) (S : Finset ι) (x : Vec d)
    (hcore : ∀ i, i ∉ S → |A * ⟪b i, x⟫_ℝ| ≤ r) :
    Model.oracle (ridgeMasked Q b τ r A T₃ T₄) x =
      Model.oracle (disclosedMasked Q b τ r A T₃ T₄ S) x := by
  classical
  rw [ridgeMasked_eq_full_disclosure]
  have hc := Primitive.disclosed_corrections b S hr x hcore
  have hv : correctionSum b τ r A Finset.univ x = correctionSum b τ r A S x :=
    congrArg (fun v => τ * v) hc.1
  have hd : fderiv ℝ (correctionSum b τ r A Finset.univ) x =
      fderiv ℝ (correctionSum b τ r A S) x := by
    have hfull := (ridgeSum_smooth b (Primitive.correction_smooth r) A).differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
    have hpart : DifferentiableAt ℝ
        (fun y => ∑ i ∈ S, Primitive.correction r (A * ⟪b i, y⟫_ℝ)) x := by
      apply DifferentiableAt.sum
      intro i _
      exact ((Primitive.correction_smooth r).comp (scaledReadout b A i).contDiff).differentiable
        (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
    unfold correctionSum
    change DifferentiableAt ℝ (fun y => ∑ i, Primitive.correction r (A * ⟪b i, y⟫_ℝ)) x at hfull
    rw [fderiv_const_mul hfull τ, fderiv_const_mul hpart τ, hc.2]
  have hbase : DifferentiableAt ℝ
      (fun y => Q y + (mask (cubicSignal τ A b + T₃) (quarticSignal τ A b + T₄) y +
        10 * τ * Fintype.card ι)) x :=
    ((hQ.add ((mask_smooth _ _).add contDiff_const)).differentiable (by norm_num)) x
  have hfull := (correctionSum_smooth b τ r A Finset.univ).differentiable
    (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  have hpart := (correctionSum_smooth b τ r A S).differentiable
    (by norm_num : (1 : WithTop ℕ∞) ≤ ∞) x
  apply Prod.ext
  · change _ + correctionSum b τ r A Finset.univ x = _ + correctionSum b τ r A S x
    rw [hv]
  · have hfd : fderiv ℝ (disclosedMasked Q b τ r A T₃ T₄ Finset.univ) x =
        fderiv ℝ (disclosedMasked Q b τ r A T₃ T₄ S) x := by
      change fderiv ℝ (fun y => Q y +
          (mask (cubicSignal τ A b + T₃) (quarticSignal τ A b + T₄) y + 10 * τ * Fintype.card ι) +
          correctionSum b τ r A Finset.univ y) x =
        fderiv ℝ (fun y => Q y +
          (mask (cubicSignal τ A b + T₃) (quarticSignal τ A b + T₄) y + 10 * τ * Fintype.card ι) +
          correctionSum b τ r A S y) x
      rw [fderiv_add hbase hfull, fderiv_add hbase hpart, hd]
    exact congrArg (InnerProductSpace.toDual ℝ (Vec d)).symm hfd

def channelResponse {d : ℕ} (Q C : Vec d → ℝ) (c : ℝ) (x Y₃ Y₄ : Vec d) : Model.Response d :=
  (Q x + (⟪Y₃, x⟫_ℝ / 3 + ⟪Y₄, x⟫_ℝ / 4 + c) + C x,
    gradient Q x + (Y₃ + Y₄) + gradient C x)

theorem channelResponse_exact {d : ℕ} {Q C : Vec d → ℝ}
    (hQ : Differentiable ℝ Q) (hC : Differentiable ℝ C) (c : ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d) :
    Model.oracle (fun y => Q y + (mask T₃ T₄ y + c) + C y) x =
      channelResponse Q C c x (channel 3 T₃ x) (channel 4 T₄ x) := by
  have hM := (mask_smooth T₃ T₄).differentiable (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
  apply Prod.ext
  · change Q x + (mask T₃ T₄ x + c) + C x = _
    rw [mask_value_channels]
    rfl
  · change gradient (fun y => Q y + (mask T₃ T₄ y + c) + C y) x = _
    rw [Confinement.gradient_add_at ((hQ x).add ((hM x).add_const c)) (hC x),
      Confinement.gradient_add_at (hQ x) ((hM x).add_const c)]
    have hc : gradient (fun y => mask T₃ T₄ y + c) x = gradient (mask T₃ T₄) x := by
      simp only [gradient, fderiv_add_const]
    rw [hc, mask_gradient_channels]
    rfl

def confineResponse {d : ℕ} (R η : ℝ) (x : Vec d) (a : Model.Response d) : Model.Response d :=
  (a.1 + η / 2 * ‖x‖ ^ 2, radialDerivative R x a.2 + η • x)

theorem confineResponse_exact {d : ℕ} {F : Vec d → ℝ}
    (hF : Differentiable ℝ F) (R η : ℝ) (x : Vec d) :
    Model.oracle (Confinement.objective F R η) x =
      confineResponse R η x (Model.oracle F (radial R x)) := by
  apply Prod.ext
  · rfl
  · exact Confinement.objective_gradient R η x (hF _)

/-- Only the actual matrix-vector response `Q x` is used in reconstructing
the quadratic oracle. The complete matrix is not exposed to the policy. -/
def quadraticResponse {d : ℕ} (x c qx : Vec d) : Model.Response d :=
  ((1 / 2 : ℝ) * ⟪x, qx⟫_ℝ + ⟪c, x⟫_ℝ, qx + c)

theorem quadraticResponse_exact {d : ℕ} (Q : Vec d →L[ℝ] Vec d) (c : Vec d)
    (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ) (x : Vec d) :
    Model.oracle (SymmetricQuadratic.energy Q (innerSL ℝ c)) x = quadraticResponse x c (Q x) := by
  apply Prod.ext
  · rfl
  · change gradient (SymmetricQuadratic.energy Q (innerSL ℝ c)) x = Q x + c
    apply (InnerProductSpace.toDual ℝ (Vec d)).injective
    rw [gradient, LinearIsometryEquiv.apply_symm_apply,
      (SymmetricQuadratic.hasFDerivAt Q (innerSL ℝ c) hsym x).fderiv]
    ext v
    simp only [ContinuousLinearMap.add_apply, innerSL_apply,
      InnerProductSpace.toDual_apply, inner_add_left]

theorem confineResponse_continuous {d : ℕ} (R η : ℝ) :
    Continuous (fun z : Vec d × Model.Response d => confineResponse R η z.1 z.2) := by
  apply Continuous.prodMk
  · exact continuous_snd.fst.add (continuous_const.mul (continuous_fst.norm.pow 2))
  · have hd : Continuous (fun x : Vec d => radialDerivative R x) := by
      have heq : (fun x : Vec d => radialDerivative R x) =
          fderiv ℝ (radial R : Vec d → Vec d) := funext fun x => (radial_fderiv R x).symm
      rw [heq]
      exact (radial_contDiff (E := Vec d) R ∞).continuous_fderiv (by norm_num)
    exact ((hd.comp continuous_fst).clm_apply continuous_snd.snd).add
      (continuous_const.smul continuous_fst)

theorem quadraticResponse_continuous (d : ℕ) :
    Continuous (fun z : Vec d × Vec d × Vec d => quadraticResponse z.1 z.2.1 z.2.2) :=
  ((continuous_const.mul (continuous_fst.inner continuous_snd.snd)).add
    (continuous_snd.fst.inner continuous_fst)).prodMk
    (continuous_snd.snd.add continuous_snd.fst)

/-- Reconstruction takes two physical tensor channels, the public matrix
response, the disclosed linear vector, and the disclosed correction oracle. -/
def dataResponse {d : ℕ} (constant : ℝ) (x c qx Y₃ Y₄ : Vec d)
    (correction : Model.Response d) : Model.Response d :=
  ((quadraticResponse x c qx).1 +
      (⟪Y₃, x⟫_ℝ / 3 + ⟪Y₄, x⟫_ℝ / 4 + constant) + correction.1,
    (quadraticResponse x c qx).2 + (Y₃ + Y₄) + correction.2)

theorem dataResponse_exact {d : ℕ} (Q : Vec d →L[ℝ] Vec d) (c : Vec d)
    (hsym : ∀ x y, ⟪x, Q y⟫_ℝ = ⟪Q x, y⟫_ℝ)
    {C : Vec d → ℝ} (hC : Differentiable ℝ C) (constant : ℝ)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d) :
    Model.oracle (fun y => SymmetricQuadratic.energy Q (innerSL ℝ c) y +
      (mask T₃ T₄ y + constant) + C y) x =
      dataResponse constant x c (Q x) (channel 3 T₃ x) (channel 4 T₄ x)
        (Model.oracle C x) := by
  rw [channelResponse_exact (fun y => (SymmetricQuadratic.hasFDerivAt Q
    (innerSL ℝ c) hsym y).differentiableAt) hC]
  have hq := quadraticResponse_exact Q c hsym x
  have hg := congrArg Prod.snd hq
  change gradient (SymmetricQuadratic.energy Q (innerSL ℝ c)) x = Q x + c at hg
  apply Prod.ext
  · rfl
  · change gradient (SymmetricQuadratic.energy Q (innerSL ℝ c)) x + _ + _ = _
    rw [hg]
    rfl

theorem dataResponse_continuous {d : ℕ} (constant : ℝ) :
    Continuous (fun z : (Fin 5 → Vec d) × Model.Response d =>
      dataResponse constant (z.1 0) (z.1 1) (z.1 2) (z.1 3) (z.1 4) z.2) := by
  have hv (i : Fin 5) : Continuous (fun z : (Fin 5 → Vec d) × Model.Response d => z.1 i) :=
    (continuous_apply i).comp continuous_fst
  exact (((continuous_const.mul ((hv 0).inner (hv 2))).add ((hv 1).inner (hv 0))).add
    (((hv 3).inner (hv 0)).div_const 3 |>.add
      (((hv 4).inner (hv 0)).div_const 4) |>.add continuous_const) |>.add continuous_snd.fst).prodMk
    ((((hv 2).add (hv 1)).add ((hv 3).add (hv 4))).add continuous_snd.snd)

end MatchingBounds1005.TensorGeometry
