import Bilevel.ChiFinePhysicalLocality

/-! Actual active/inactive fine potentials at arbitrary normal arguments.
The physical latent support is transported through the actual radial/frame
map, including the public query direction in the disclosed subspace. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain CompensatedMean ZeroChainSchedule

theorem finite_weighted_gradient_support {n : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Space n → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i)) (w : ι → ℝ)
    (z : Space n) (j : Fin (n+1)) (hs : ∀ i,i∈S → gradient (f i) z j=0) :
    gradient (fun x => ∑ i ∈ S,f i x*w i) z j=0 := by
  have hd (i : ι) := ((hf i).differentiable (by norm_num) z).hasGradientAt.hasFDerivAt
  have hh := HasFDerivAt.sum (u:=S) (fun i _ => (hd i).mul_const (w i))
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hh]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [ContinuousLinearMap.smul_apply,← ZeroChainResidualLocality.gradient_coordinate_eq (hd i),hs i hi,smul_zero]

namespace Parameters
variable (P : Parameters)

def activeSlice (n : ℕ) (lambdaExt s : ℝ) (z : Space n) : ℝ :=
  P.coupling n lambdaExt (pack (Space n) z s 0)

def inactiveSlice (n : ℕ) (lambdaExt s : ℝ) (z : Space n) : ℝ :=
  P.inactiveCoupling n lambdaExt (pack (Space n) z s 0)

theorem activeSlice_sum (n : ℕ) (lambdaExt s : ℝ) (z : Space n) :
    P.activeSlice n lambdaExt s z=∑ k ∈ Finset.range (levels P.θ+1),
      P.pieces n k z*(lambdaExt*SmallGapProfiles.normal (width P.c P.β P.θ k) s) := by
  simp only [activeSlice,coupling,CompensatedMean.Data.coupling,CompensatedMean.Data.couplingTerm,
    data,uProj_pack,sProj_pack]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem inactiveSlice_sum (n : ℕ) (lambdaExt s : ℝ) (z : Space n) :
    P.inactiveSlice n lambdaExt s z=∑ k ∈ Finset.range (levels P.θ+1),
      P.inactivePiece n k z*(lambdaExt*SmallGapProfiles.normal (width P.c P.β P.θ k) s) := by
  classical
  have hact := P.activeSlice_sum n lambdaExt s z
  simp only [inactivePiece,sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,
    Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_self,if_true]
  rw [← hact]
  simp only [inactiveSlice,inactiveCoupling,signal,uProj_pack,sProj_pack]
  change P.activeSlice n lambdaExt s z-lambdaExt*P.residualDifference n z*
    SmallGapProfiles.normal P.finalWidth s=P.activeSlice n lambdaExt s z-
      P.residualDifference n z*(lambdaExt*SmallGapProfiles.normal P.finalWidth s)
  ring

theorem activeSlice_contDiff (n : ℕ) (lambdaExt s : ℝ) : ContDiff ℝ 3 (P.activeSlice n lambdaExt s) := by
  have he := funext (P.activeSlice_sum n lambdaExt s)
  rw [he]
  exact ContDiff.sum (fun k _ => (P.pieces_contDiff n k).mul contDiff_const)

theorem inactiveSlice_contDiff (n : ℕ) (lambdaExt s : ℝ) : ContDiff ℝ 3 (P.inactiveSlice n lambdaExt s) := by
  have he := funext (P.inactiveSlice_sum n lambdaExt s)
  rw [he]
  exact ContDiff.sum (fun k _ => (P.inactivePiece_contDiff n k).mul contDiff_const)

theorem activeSlice_gradient_support (n r : ℕ) (lambdaExt s : ℝ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤P.β/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (P.activeSlice n lambdaExt s) z j=0 := by
  rw [funext (P.activeSlice_sum n lambdaExt s)]
  exact finite_weighted_gradient_support _ _ (P.pieces_contDiff n) _ z j
    (fun k _ => P.pieces_gradient_support n k r z hz j hj)

theorem inactiveSlice_gradient_support (n r : ℕ) (lambdaExt s : ℝ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤P.signalResolution)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (P.inactiveSlice n lambdaExt s) z j=0 := by
  rw [funext (P.inactiveSlice_sum n lambdaExt s)]
  exact finite_weighted_gradient_support _ _ (P.inactivePiece_contDiff n) _ z j
    (fun k hk => P.inactivePiece_gradient_support n k r (by have := Finset.mem_range.mp hk;omega) z hz j hj)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem carried_activeSlice_gradient_mem (n r : ℕ) (lambdaExt s R : ℝ) (hR : 0<R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (W : Submodule ℝ E) (hu : u∈W)
    (hU : ∀ j : Fin (n+1),j.val<r+1 → U (basis j)∈W)
    (hz : ∀ j : Fin (n+1),r≤j.val → |WrappedChain.coordinates n R U u j|≤P.β/4) :
    gradient (P.activeSlice n lambdaExt s ∘ WrappedChain.coordinates n R U) u∈W :=
  WrappedPrefixLocality.carried_gradient_mem n (r+1) R hR U _
    ((P.activeSlice_contDiff n lambdaExt s).differentiable (by norm_num)) u W hu hU
    (fun j hj => P.activeSlice_gradient_support n r lambdaExt s _ hz j hj)

theorem carried_inactiveSlice_gradient_mem (n r : ℕ) (lambdaExt s R : ℝ) (hR : 0<R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E) (W : Submodule ℝ E) (hu : u∈W)
    (hU : ∀ j : Fin (n+1),j.val<r → U (basis j)∈W)
    (hz : ∀ j : Fin (n+1),r≤j.val → |WrappedChain.coordinates n R U u j|≤P.signalResolution) :
    gradient (P.inactiveSlice n lambdaExt s ∘ WrappedChain.coordinates n R U) u∈W :=
  WrappedPrefixLocality.carried_gradient_mem n r R hR U _
    ((P.inactiveSlice_contDiff n lambdaExt s).differentiable (by norm_num)) u W hu hU
    (fun j hj => P.inactiveSlice_gradient_support n r lambdaExt s _ hz j hj)

end Parameters
end Bilevel.ChiFine
