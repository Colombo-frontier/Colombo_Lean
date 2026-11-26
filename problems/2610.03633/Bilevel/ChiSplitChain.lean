import Bilevel.ChiBoundedChainCentered
import Bilevel.ChiBoundedChainEstimates
import Bilevel.ChiPrimitiveAssembly

/-! The actual split-endpoint chain. Source coordinates and predecessor
coordinates are separate off the response graph. On the diagonal this is
exactly the original bounded chain, including its centered frontier. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ZeroChainPotential PrimitiveGeometry PartialLegendre

abbrev Latent (n : ℕ) := Joint (Space n) (Space n)

def sourceProjection {n : ℕ} (i : Fin (n+1)) : Latent n →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜:=ℝ) i).comp jointFstLinear

def targetProjection {n : ℕ} (i : Fin (n+1)) : Latent n →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜:=ℝ) i).comp jointSndLinear

theorem sourceProjection_apply {n : ℕ} (i : Fin (n+1)) (z : Latent n) :
    sourceProjection i z=z.fst i := rfl

theorem targetProjection_apply {n : ℕ} (i : Fin (n+1)) (z : Latent n) :
    targetProjection i z=z.snd i := rfl

def value (n : ℕ) (z : Latent n) : ℝ :=
  -phi (z.fst 0)+∑ i : Fin n,edge (z.snd i.castSucc) (z.fst i.succ)

def frontier (n : ℕ) (z : Latent n) : ℝ :=
  ∑ i : Fin (n+1),-selector n i z.snd*(phi (z.fst i)-phi 0)

def carrier (n : ℕ) (z : Latent n) : ℝ := value n z-frontier n z

def chain (n : ℕ) (ell h : ℝ) (z : Latent n) : ℝ := ell*h^2*value n (h⁻¹ • z)

def sourceGradient (n : ℕ) (z : Latent n) : Space n :=
  -phiSlope (z.fst 0) • basis 0+
    ∑ i : Fin n,edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ

def targetGradient (n : ℕ) (z : Latent n) : Space n :=
  ∑ i : Fin n,edgeLeft (z.snd i.castSucc) (z.fst i.succ) • basis i.castSucc

theorem value_diagonal (n : ℕ) (z : Space n) : value n (pack z z)=ChiBoundedChain.value n z := rfl

theorem frontier_diagonal (n : ℕ) (z : Space n) : frontier n (pack z z)=centeredResidual n z := rfl

theorem carrier_diagonal (n : ℕ) (z : Space n) : carrier n (pack z z)=centeredCarrier n z := rfl

theorem chain_diagonal (n : ℕ) (ell h : ℝ) (z : Space n) :
    chain n ell h (pack z z)=ChiBoundedChain.chain n ell h z := rfl

theorem frontier_zero (n : ℕ) : frontier n 0=0 := by simp [frontier]

theorem value_contDiff (n k : ℕ) : ContDiff ℝ k (value n) := by
  have hs (i : Fin n) : ContDiff ℝ k (fun z : Latent n => edge (z.snd i.castSucc) (z.fst i.succ)) := by
    have hi := (targetProjection i.castSucc).contDiff (n:=k)
    have hj := (sourceProjection i.succ).contDiff (n:=k)
    exact ((psi_contDiff.comp hi.neg).mul ((phi_contDiff k).comp hj.neg)).sub
      ((psi_contDiff.comp hi).mul ((phi_contDiff k).comp hj))
  exact (((phi_contDiff k).comp (sourceProjection (0:Fin (n+1))).contDiff).neg).add
    (ContDiff.sum (fun i _ => hs i))

theorem frontier_contDiff (n k : ℕ) : ContDiff ℝ k (frontier n) := by
  apply ContDiff.sum
  intro i _
  exact (((selector_contDiff n k i).comp (jointSndLinear : Latent n →L[ℝ] Space n).contDiff).neg).mul
    (((phi_contDiff k).comp (sourceProjection i).contDiff).sub contDiff_const)

theorem chain_contDiff (n k : ℕ) (ell h : ℝ) : ContDiff ℝ k (chain n ell h) :=
  contDiff_const.mul ((value_contDiff n k).comp (contDiff_id.const_smul h⁻¹))

theorem edge_hasFDerivAt {n : ℕ} (i : Fin n) (z : Latent n) :
    HasFDerivAt (fun w : Latent n => edge (w.snd i.castSucc) (w.fst i.succ))
      (edgeLeft (z.snd i.castSucc) (z.fst i.succ) • targetProjection i.castSucc+
        edgeRight (z.snd i.castSucc) (z.fst i.succ) • sourceProjection i.succ) z := by
  have hp (t : ℝ) : HasDerivAt psi (deriv psi t) t := by rw [psi_deriv]; exact psi_hasDerivAt t
  have hi := (targetProjection i.castSucc).hasFDerivAt (x:=z)
  have hj := (sourceProjection i.succ).hasFDerivAt (x:=z)
  have hm0 := (hp (-z.snd i.castSucc)).hasFDerivAt.comp z hi.neg
  have hm1 := (phi_hasDerivAt (-z.fst i.succ)).hasFDerivAt.comp z hj.neg
  have hp0 := (hp (z.snd i.castSucc)).hasFDerivAt.comp z hi
  have hp1 := (phi_hasDerivAt (z.fst i.succ)).hasFDerivAt.comp z hj
  convert (hm0.mul hm1).sub (hp0.mul hp1) using 1
  ext v
  simp [edgeLeft,edgeRight,ContinuousLinearMap.comp_apply,sourceProjection_apply,targetProjection_apply]
  ring

theorem value_hasFDerivAt (n : ℕ) (z : Latent n) :
    HasFDerivAt (value n)
      ((-phiSlope (z.fst 0)) • sourceProjection 0+
        ∑ i : Fin n,(edgeLeft (z.snd i.castSucc) (z.fst i.succ) • targetProjection i.castSucc+
          edgeRight (z.snd i.castSucc) (z.fst i.succ) • sourceProjection i.succ)) z := by
  have h0 := ((phi_hasDerivAt (z.fst 0)).hasFDerivAt.comp z (sourceProjection 0).hasFDerivAt).neg
  have hs := HasFDerivAt.sum (fun (i : Fin n) (_ : i∈Finset.univ) => edge_hasFDerivAt i z)
  convert h0.add hs using 1
  ext v
  simp [ContinuousLinearMap.comp_apply,sourceProjection_apply]
  ring

theorem value_hasGradientAt (n : ℕ) (z : Latent n) :
    HasGradientAt (value n) (pack (sourceGradient n z) (targetGradient n z)) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert value_hasFDerivAt n z using 1
  ext v
  simp only [InnerProductSpace.toDual_apply,WithLp.prod_inner_apply]
  change ⟪sourceGradient n z,v.fst⟫+⟪targetGradient n z,v.snd⟫= _
  simp only [sourceGradient,targetGradient,
    inner_add_left,real_inner_smul_left,sum_inner,inner_basis,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    sourceProjection_apply,targetProjection_apply,smul_eq_mul]
  rw [Finset.sum_add_distrib]
  ring

theorem actual_gradient (n : ℕ) (z : Latent n) :
    gradient (value n) z=pack (sourceGradient n z) (targetGradient n z) :=
  (value_hasGradientAt n z).gradient

theorem value_abs_bound (n : ℕ) (z : Latent n) : |value n z|≤(n+1)*gaussianBound := by
  have hp : |phi (z.fst 0)|≤gaussianBound := by
    rw [abs_of_nonneg (phi_nonneg _)]; exact phi_bounded _
  calc
    _≤|-phi (z.fst 0)|+|∑ i : Fin n,edge (z.snd i.castSucc) (z.fst i.succ)| := abs_add _ _
    _≤gaussianBound+∑ i : Fin n,|edge (z.snd i.castSucc) (z.fst i.succ)| :=
      add_le_add (by simpa only [abs_neg] using hp) (Finset.abs_sum_le_sum_abs ..)
    _≤gaussianBound+∑ _ : Fin n,gaussianBound := add_le_add_left
      (Finset.sum_le_sum (fun i _ => edge_abs_bound _ _)) _
    _=(n+1)*gaussianBound := by simp; ring

end Bilevel.ChiSplitChain
