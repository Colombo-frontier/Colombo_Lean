import Bilevel.EndpointTransportLower
import Bilevel.ChiHybridCorrection

/-! Euclidean block-diagonal operators for the heterogeneous transport
tangent and normal spaces. Bounds use maxima, not sums over blocks. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre
variable {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]

def jointOperator (S : A →L[ℝ] A) (T : B →L[ℝ] B) : Joint A B →L[ℝ] Joint A B :=
  packLinear.comp ((S.comp jointFstLinear).prod (T.comp jointSndLinear))

theorem jointOperator_apply (S : A →L[ℝ] A) (T : B →L[ℝ] B) (z : Joint A B) :
    jointOperator S T z=pack (S z.fst) (T z.snd) := rfl

theorem jointOperator_symmetric (S : A →L[ℝ] A) (T : B →L[ℝ] B)
    (hS : ∀ u v,⟪S u,v⟫=⟪u,S v⟫) (hT : ∀ u v,⟪T u,v⟫=⟪u,T v⟫) (z w : Joint A B) :
    ⟪jointOperator S T z,w⟫=⟪z,jointOperator S T w⟫ := by
  change ⟪S z.fst,w.fst⟫+⟪T z.snd,w.snd⟫=⟪z.fst,S w.fst⟫+⟪z.snd,T w.snd⟫
  rw [hS,hT]

theorem jointOperator_coercive (S : A →L[ℝ] A) (T : B →L[ℝ] B) (m : ℝ)
    (hS : ∀ u,m*‖u‖^2≤⟪u,S u⟫) (hT : ∀ v,m*‖v‖^2≤⟪v,T v⟫) (z : Joint A B) :
    m*‖z‖^2≤⟪z,jointOperator S T z⟫ := by
  rw [norm_sq]
  change m*(‖z.fst‖^2+‖z.snd‖^2)≤⟪z.fst,S z.fst⟫+⟪z.snd,T z.snd⟫
  linarith only [hS z.fst,hT z.snd]

theorem jointOperator_norm_bound (S : A →L[ℝ] A) (T : B →L[ℝ] B)
    {K : ℝ} (hK : 0≤K) (hS : ‖S‖≤K) (hT : ‖T‖≤K) : ‖jointOperator S T‖≤K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro z
  have hs := (S.le_opNorm z.fst).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
  have ht := (T.le_opNorm z.snd).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hs' := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr hs
  have ht' := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mpr ht
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  rw [jointOperator_apply,norm_sq,mul_pow,norm_sq]
  change ‖S z.fst‖^2+‖T z.snd‖^2≤K^2*(‖z.fst‖^2+‖z.snd‖^2)
  nlinarith only [hs',ht']

theorem scalarIdentity_norm (m : ℝ) : ‖m • ContinuousLinearMap.id ℝ A‖≤|m| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg m)
  intro z
  change ‖m • z‖≤|m| * ‖z‖
  rw [norm_smul,Real.norm_eq_abs]

end Bilevel.EndpointTransportResponse
