import Bilevel.ChiOuterCarrierLedger

/-! Mixed jets of the actual one-sided macro release correction. The
selector support removes any factor equal to the number of macro stages. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ZeroChainPotential

theorem outer_residual_contDiff (n : ℕ) (i : Fin (n+1)) : ContDiff ℝ 3 (residualTerm n i) :=
  (selector_contDiff n 3 i).neg.mul ((phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

theorem outer_residual_uniform_jets : ∃ B : ℝ,1≤B ∧ ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n)
    (k : ℕ),k≤3 → ‖iteratedFDeriv ℝ k (residualTerm n i) z‖≤B := by
  obtain ⟨S,hS,hs⟩ := selector_uniform_jets
  obtain ⟨K,hK,hprof⟩ := chain_profile_bound
  have hS0 : 0≤S := by linarith
  have hK0 : 0≤K := by linarith
  refine ⟨8*S*K,by nlinarith [mul_le_mul hS hK zero_le_one hS0],fun n i z k hk => ?_⟩
  have hf : ContDiff ℝ 3 (fun y : Space n => -selector n i y) := (selector_contDiff n 3 i).neg
  have hg : ContDiff ℝ 3 (fun y : Space n => phi (y i)) := (phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff
  have hb := same_width_product_jets hf hg S K 1 hS0 hK0 (by norm_num) z k hk
    (fun q hq => by
      change ‖iteratedFDeriv ℝ q (-(selector n i)) z‖≤S/1^q
      rw [iteratedFDeriv_neg_apply,norm_neg]
      simpa only [one_pow,div_one] using hs n i z q (by omega))
    (fun q hq => by
      simpa only [one_pow,div_one] using ZeroChainResidualBounds.scalar_linear_jet_bound (phi_contDiff 3)
        (EuclideanSpace.proj (𝕜:=ℝ) i) (ZeroChainResidualBounds.projection_norm_le i) z q (by omega) K hK0
        (hprof ⟨q,by omega⟩ (z i)).2)
  simpa only [one_pow,div_one] using hb

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def outerReleaseCorrection (m : ℕ) (M : Node E) (kids : Fin (M.n+1) → Node F)
    (z : Joint E (Blocks m F)) : ℝ :=
  ∑ i : Fin (M.n+1),wrappedResidual M i z.fst*(jointRelease m 0 (kids i) z.snd-1)

def outerIncomingFactor (m : ℕ) (M : Node E) (i : Fin (M.n+1)) (z : Joint E (Blocks m F)) : ℝ :=
  -(M.ell*M.width^2)*phi (M.coordinates z.fst i/M.width)

omit [CompleteSpace F] in
theorem outerIncomingFactor_contDiff (m : ℕ) (M : Node E) (i : Fin (M.n+1)) :
    ContDiff ℝ 3 (outerIncomingFactor (F:=F) m M i) :=
  contDiff_const.mul ((phi_contDiff 3).comp
    ((((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp (M.coordinates_contDiff 3)).comp
      (outerProjection (E:=E) (F:=F) m).contDiff).div_const M.width))

theorem outerReleaseCorrection_contDiff (m : ℕ) (M : Node E) (kids : Fin (M.n+1) → Node F) :
    ContDiff ℝ 3 (outerReleaseCorrection m M kids) :=
  ContDiff.sum (fun i _ => ((wrappedResidual_contDiff M i 3).comp
    (outerProjection (E:=E) (F:=F) m).contDiff).mul
    (((jointRelease_contDiff m 0 (kids i) 3).comp (innerProjection (E:=E) (F:=F) m).contDiff).sub contDiff_const))

omit [CompleteSpace F] in
theorem outerResidual_factor (m : ℕ) (M : Node E) (i : Fin (M.n+1)) (z : Joint E (Blocks m F)) :
    wrappedResidual M i z.fst=jointOuterSelector m M i z*outerIncomingFactor m M i z := by
  change (M.ell*M.width^2)*(-selector M.n i (M.width⁻¹ • M.coordinates z.fst)*
    phi ((M.width⁻¹ • M.coordinates z.fst) i))=
    selector M.n i (M.width⁻¹ • M.coordinates z.fst)*(-(M.ell*M.width^2)*phi (M.coordinates z.fst i/M.width))
  simp only [PiLp.smul_apply,smul_eq_mul,div_eq_inv_mul]
  ring

omit [CompleteSpace F] in
theorem outer_selected_joint_sum_bound (m : ℕ) (M : Node E)
    (f : Fin (M.n+1) → Joint E (Blocks m F) → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (z : Joint E (Blocks m F)) (k : ℕ) (hk : k≤3) (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y => jointOuterSelector m M i y*f i y) z‖≤B) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i : Fin (M.n+1),jointOuterSelector m M i y*f i y) z‖≤B := by
  rw [iteratedFDeriv_sum (fun i _ => ((jointOuterSelector_contDiff m M i).mul (hf i)).of_le
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_exclusive _ B hB hb
  intro i j hij hi
  by_contra hj
  have hsupport (a : Fin (M.n+1))
      (ha : iteratedFDeriv ℝ k (fun y => jointOuterSelector m M a y*f a y) z≠0) :
      ∃ q≤k,iteratedFDeriv ℝ q (jointOuterSelector m M a) z≠0 := by
    by_contra! hz
    exact ha (ZeroChainResidualBounds.jet_mul_zero_left (jointOuterSelector_contDiff m M a) (hf a) z k hk hz)
  obtain ⟨a,ha,hai⟩ := hsupport i hi
  obtain ⟨b,hb,hbj⟩ := hsupport j hj
  exact hij (jointOuterSelector_jets_unique m M i j z a b (by omega) (by omega) hai hbj)

theorem constructed_outer_residual_jets : ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (M : Node E),0≤M.ell → 0<M.width → M.width≤M.radius →
      ∀ m i (z : Joint E (Blocks m F)) k,k≤3 →
      ‖iteratedFDeriv ℝ k (fun y : Joint E (Blocks m F) => wrappedResidual M i y.fst) z‖≤
        C*(M.ell*M.width^2)/M.width^k := by
  obtain ⟨B,hB,hraw⟩ := outer_residual_uniform_jets
  have hB0 : 0≤B := by linarith
  refine ⟨100000*B,by linarith,fun E F _ _ _ _ _ _ M hell hh hhR m i z k hk => ?_⟩
  apply (contraction_jet_bound (outerProjection (E:=E) (F:=F) m) (outerProjection_norm_le m)
    (wrappedResidual_contDiff M i 3) z k hk).trans
  exact scaled_radial_profile_jet_bound (outer_residual_contDiff M.n i) B (M.ell*M.width^2) M.width M.radius
    hB0 (by positivity) hh hhR (fun q hq y => hraw M.n i y q hq) M.frame z.fst k hk

end Bilevel.ChiOuter
