import Bilevel.ChiSplitChainRegularity
import Bilevel.ChiBoundedChainSize
import Bilevel.ChiBoundedChainCompositionBounds

/-! Actual global first-derivative budget for the split chain. The bound grows
only as the square root of the number of chain coordinates. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitChain
open ChiBoundedChain ChiBoundedChain.Regularity ChiBoundedChain.Size ZeroChainPotential PrimitiveGeometry

theorem norm_coefficients_uniform_le {n : ℕ} (f : Fin n → Fin (n+1))
    (hf : Function.Injective f) (a : Fin n → ℝ) {A : ℝ} (hA : 0≤A)
    (ha : ∀ i,|a i|≤A) : ‖∑ i,a i • basis (f i)‖≤A*Real.sqrt ((n:ℝ)+1) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sum_basis_sq f hf,mul_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)+1)]
  calc
    _≤∑ _ : Fin n,A^2 := Finset.sum_le_sum (fun i _ => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hA).mpr (ha i))
    _≤_ := by simp; nlinarith [sq_nonneg A]

theorem gradient_norm_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (z : Latent n),
    ‖gradient (value n) z‖≤C*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨K,hK,hpsi⟩ := psi_common_bound
  have hG := gaussianBound_nonneg
  have hψ : ∀ t,|deriv psi t|≤K := by
    intro t
    simpa only [Fin.val_one,iteratedDeriv_one] using hpsi 1 t
  refine ⟨3*Real.sqrt (Real.exp 1)+2*K*gaussianBound,by positivity,fun n z => ?_⟩
  have hr := norm_coefficients_uniform_le Fin.succ (Fin.succ_injective n)
    (fun i => edgeRight (z.snd i.castSucc) (z.fst i.succ))
    (by positivity : 0≤2*1*Real.sqrt (Real.exp 1)) (fun i => edgeRight_abs_bound _ _)
  have hl := norm_coefficients_uniform_le Fin.castSucc (Fin.castSucc_injective n)
    (fun i => edgeLeft (z.snd i.castSucc) (z.fst i.succ))
    (by positivity : 0≤2*K*gaussianBound) (fun i => edgeLeft_abs_bound K hK.le hψ _ _)
  have hbase : ‖(-phiSlope (z.fst 0)) • (basis 0 : Space n)‖≤Real.sqrt (Real.exp 1) := by
    simpa only [norm_smul,basis,EuclideanSpace.norm_single,norm_one,mul_one,
      Real.norm_eq_abs,abs_neg,phi_deriv] using phi_first_bound (z.fst 0)
  have hsqrt : 1≤Real.sqrt ((n:ℝ)+1) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simp)
  have hbase' := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (Real.exp 1))
  have hs := norm_add_le ((-phiSlope (z.fst 0)) • (basis 0 : Space n))
    (∑ i : Fin n,edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ)
  rw [actual_gradient]
  apply (latent_norm_le _ _).trans
  change ‖(-phiSlope (z.fst 0)) • (basis 0 : Space n)+
    ∑ i : Fin n,edgeRight (z.snd i.castSucc) (z.fst i.succ) • basis i.succ‖+
    ‖∑ i : Fin n,edgeLeft (z.snd i.castSucc) (z.fst i.succ) • basis i.castSucc‖≤_
  nlinarith only [hbase,hbase',hs,hr,hl]

theorem chain_first_uniform : ∃ C : ℝ,0≤C ∧ ∀ (n : ℕ) (ell h : ℝ),
    0≤ell → 0<h → ∀ z : Latent n,
      ‖iteratedFDeriv ℝ 1 (chain n ell h) z‖≤C*(ell*h)*Real.sqrt ((n:ℝ)+1) := by
  obtain ⟨C,hC,hb⟩ := gradient_norm_uniform
  refine ⟨C,hC,fun n ell h hell hh z => ?_⟩
  have ht := scaled_jet_bound (value_contDiff n 3) (ell*h^2) h
    (C*Real.sqrt ((n:ℝ)+1)) (by positivity) hh 1 (by norm_num)
    (fun w => by rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq]; exact hb n w) z
  change ‖iteratedFDeriv ℝ 1 (chain n ell h) z‖≤_ at ht
  convert ht using 1
  field_simp
  ring

end Bilevel.ChiSplitChain
