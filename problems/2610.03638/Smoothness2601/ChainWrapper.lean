import Smoothness2601.ExtensiveBounds
import Smoothness2601.ChainLocality
import Smoothness2601.RadialBarrier

/-! The actual split chain in an arbitrary orthonormal frame, with the
quadratic radial wrapper and an arbitrary-query gradient barrier. -/
noncomputable section
namespace Smoothness2601.ExtensiveChain
open Cutoffs ChainProfiles Finset RadialWrapper
open scoped BigOperators RealInnerProductSpace Topology ContDiff

theorem frontierGradientBound_nonneg : 0 ≤ frontierGradientBound := by
  unfold frontierGradientBound
  have hL := bumpData.L_nonneg
  positivity

theorem frontierHessianBound_nonneg : 0 ≤ frontierHessianBound := by
  unfold frontierHessianBound
  have hC := gateData.C_nonneg
  have hM := gateData.M_nonneg
  have hL := bumpData.L_nonneg
  have hK := bumpData.K_nonneg
  positivity

theorem frontier_gradient_lip {n : ℕ} (z w : Space n) :
    ‖gradient Cutoffs.frontier z-gradient Cutoffs.frontier w‖ ≤ frontierHessianBound*‖z-w‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x (_ : x ∈ Set.univ) => (actual_frontier_differentiable x).2)
    (fun x (_ : x ∈ Set.univ) => (actual_frontier_bounds x).2.2)
    convex_univ (Set.mem_univ w) (Set.mem_univ z)

theorem chain_gradient_bound {M K : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (z : Space n) :
    ‖gradient (chain M) z‖ ≤ (K+4*K^2+frontierGradientBound)*Real.sqrt (n+1) := by
  rw [chain_gradient]
  have ha := extensive_gradient_bound h z
  have hb := (actual_frontier_bounds z).2.1
  have hs : 1 ≤ Real.sqrt (n+1 : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
  have hb' := mul_le_mul_of_nonneg_left hs frontierGradientBound_nonneg
  have ht := norm_add_le (gradient (extensive M) z) (gradient Cutoffs.frontier z)
  nlinarith

theorem chain_gradient_lip {M K : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (z w : Space n) :
    ‖gradient (chain M) z-gradient (chain M) w‖ ≤ (K+8*K^2+frontierHessianBound)*‖z-w‖ := by
  rw [chain_gradient,chain_gradient]
  have he : gradient (extensive M) z+gradient Cutoffs.frontier z-
      (gradient (extensive M) w+gradient Cutoffs.frontier w) =
      (gradient (extensive M) z-gradient (extensive M) w)+
      (gradient Cutoffs.frontier z-gradient Cutoffs.frontier w) := by abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (extensive_gradient_norm_sub_le h z w)
    (frontier_gradient_lip z w)).trans_eq (by ring))

def chainAmplitude : ℝ := 2+frontierGradientBound

theorem chainAmplitude_nonneg : 0 ≤ chainAmplitude := by
  unfold chainAmplitude
  linarith [frontierGradientBound_nonneg]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def frameProjection {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : E →L[ℝ] Space n :=
  U.toContinuousLinearMap.adjoint

theorem frameProjection_norm {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : ‖frameProjection U‖ ≤ 1 := by
  rw [frameProjection,LinearIsometryEquiv.norm_map]
  exact U.norm_toContinuousLinearMap_le

theorem frameProjection_adjoint {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) :
    (frameProjection U).adjoint = U.toContinuousLinearMap :=
  ContinuousLinearMap.adjoint_adjoint _

def chainRadius (CH : ℝ) (n : ℕ) : ℝ := 64*CH*Real.sqrt (n+1)

def wrappedA (CH M : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : E → ℝ :=
  RadialWrapper.wrapped (chainRadius CH n) (1/16) (frameProjection U) (extensive M)

def wrappedB (CH : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : E → ℝ :=
  RadialWrapper.carried (chainRadius CH n) (frameProjection U) Cutoffs.frontier

def wrappedH (CH M : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : E → ℝ :=
  RadialWrapper.wrapped (chainRadius CH n) (1/16) (frameProjection U) (chain M)

theorem wrappedH_split (CH M : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (w : E) :
    wrappedH CH M U w = wrappedA CH M U w+wrappedB CH U w := by
  unfold wrappedH wrappedA wrappedB RadialWrapper.wrapped RadialWrapper.carried chain
  ring

theorem wrappedA_contDiff (CH M : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (k : ℕ) :
    ContDiff ℝ k (wrappedA CH M U) :=
  RadialWrapper.wrapped_contDiff _ _ _ _ k ((extensive_contDiff M n).of_le
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))

theorem wrappedB_contDiff (CH : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (k : ℕ) :
    ContDiff ℝ k (wrappedB CH U) :=
  RadialWrapper.carried_contDiff _ _ _ k (frontier_contDiff.of_le
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))

theorem wrappedH_contDiff (CH M : ℝ) {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (k : ℕ) :
    ContDiff ℝ k (wrappedH CH M U) :=
  RadialWrapper.wrapped_contDiff _ _ _ _ k ((chain_contDiff M n).of_le
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))

theorem wrapped_chain_gradient_barrier {M CH : ℝ} (hM : 0 ≤ M)
    (hlarge : 2+frontierGradientBound ≤ M) (hCH : 1 ≤ CH)
    {n : ℕ} (U : Space n →ₗᵢ[ℝ] E)
    (hgrad : ∀ z : Space n, ‖gradient (chain M) z‖ ≤ CH*Real.sqrt (n+1)) (w : E)
    (hhidden : ∃ j : Fin (n+1), |frameProjection U (Bilevel.RadialWrapper.compress (chainRadius CH n) w) j| < 1) :
    (1/2:ℝ) ≤ ‖gradient (wrappedH CH M U) w‖ := by
  classical
  let z := frameProjection U (Bilevel.RadialWrapper.compress (chainRadius CH n) w)
  let s : Finset (Fin (n+1)) := univ.filter fun i => |z i| < 1
  have hs : s.Nonempty := by
    obtain ⟨j,hj⟩ := hhidden
    exact ⟨j,mem_filter.mpr ⟨mem_univ j,hj⟩⟩
  let k := s.min' hs
  have hk : |z k| < 1 := (mem_filter.mp (min'_mem s hs)).2
  have hfirst : ∀ j : Fin (n+1), j < k → 1 ≤ |z j| := by
    intro j hj
    by_contra hn
    have hmem : j ∈ s := mem_filter.mpr ⟨mem_univ j,lt_of_not_ge hn⟩
    exact (not_le_of_gt hj) (min'_le s j hmem)
  have hgk := chain_frontier_nonstationary hM hlarge z k hfirst hk
  let q := U (gradient (chain M) z)
  let u := U (EuclideanSpace.single k 1)
  have hq : ‖q‖ ≤ CH*Real.sqrt (n+1) := by simpa [q] using hgrad z
  have hu : ‖u‖ = 1 := by simp [u]
  have hic : ⟪q,u⟫ ≤ -1 := by
    simpa [q,u,EuclideanSpace.inner_single_right] using hgk
  have hiz : |⟪Bilevel.RadialWrapper.compress (chainRadius CH n) w,u⟫| ≤ 1 := by
    have he : ⟪Bilevel.RadialWrapper.compress (chainRadius CH n) w,u⟫ = z k := by
      dsimp [u,z,frameProjection]
      change ⟪Bilevel.RadialWrapper.compress (chainRadius CH n) w,
        U.toContinuousLinearMap (EuclideanSpace.single k 1)⟫ = _
      rw [← ContinuousLinearMap.adjoint_inner_left]
      simp [EuclideanSpace.inner_single_left,real_inner_comm]
    rw [he]
    exact hk.le
  have hG : 1 ≤ CH*Real.sqrt (n+1 : ℝ) := by
    have ht : 1 ≤ Real.sqrt (n+1 : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
    nlinarith
  have hb := RadialWrapper.arbitrary_query_barrier hG
    (show chainRadius CH n = 64*(CH*Real.sqrt (n+1)) by unfold chainRadius; ring) w q u hq hu hiz hic
  have hactual := RadialWrapper.wrapped_hasGradientAt (chainRadius CH n) (1/16) (frameProjection U)
    (chain M) (gradient (chain M)) (fun x => ((chain_contDiff M n).differentiable (by norm_num) x).hasGradientAt) w
  unfold wrappedH
  rw [hactual.gradient]
  simpa only [RadialWrapper.wrappedGradient,RadialWrapper.carriedGradient,frameProjection_adjoint] using hb

theorem wrapped_split_uniform_bounds {M K CH : ℝ} (h : ActualProfileControl M K)
    (hCH : 1 ≤ CH) (hbig : K+4*K^2+frontierGradientBound ≤ CH)
    {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (w : E) :
    |wrappedB CH U w| ≤ 1/4 ∧
    ‖gradient (wrappedB CH U) w‖ ≤ frontierGradientBound ∧
    ‖fderiv ℝ (gradient (wrappedB CH U)) w‖ ≤ frontierHessianBound+1/16 ∧
    ‖fderiv ℝ (gradient (wrappedA CH M U)) w‖ ≤ K+8*K^2+1/8 := by
  let G := CH*Real.sqrt (n+1 : ℝ)
  have hs : 1 ≤ Real.sqrt (n+1 : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num)
  have hG : 0 < G := by dsimp [G]; positivity
  have hR : 0 < chainRadius CH n := by unfold chainRadius; positivity
  have hratio : 4*G/chainRadius CH n = 1/16 := by
    have he : chainRadius CH n = 64*G := by dsimp [G,chainRadius]; ring
    rw [he]
    field_simp
    ring
  have hAG : K+4*K^2 ≤ CH := by linarith [frontierGradientBound_nonneg]
  have hBG : frontierGradientBound ≤ G := by
    have hb : frontierGradientBound ≤ CH := by nlinarith [h.nonnegative,sq_nonneg K]
    exact hb.trans (le_mul_of_one_le_right (by linarith) hs)
  have haGrad : ∀ z : Space n, ‖gradient (extensive M) z‖ ≤ G := fun z =>
    (extensive_gradient_bound h z).trans (mul_le_mul_of_nonneg_right hAG (Real.sqrt_nonneg _))
  have hbGrad : ∀ z : Space n, ‖gradient Cutoffs.frontier z‖ ≤ G := fun z =>
    (actual_frontier_bounds z).2.1.trans hBG
  have haDeriv : ∀ z : Space n, HasGradientAt (extensive M) (gradient (extensive M) z) z :=
    fun z => (extensive_hasFDerivAt M z).differentiableAt.hasGradientAt
  have hbDeriv : ∀ z : Space n, HasGradientAt Cutoffs.frontier (gradient Cutoffs.frontier z) z :=
    fun z => (actual_frontier_differentiable z).1.hasGradientAt
  refine ⟨(actual_frontier_bounds _).1,?_,?_,?_⟩
  · change ‖gradient (RadialWrapper.carried _ _ Cutoffs.frontier) w‖ ≤ _
    rw [(RadialWrapper.carried_hasGradientAt _ _ _ _ hbDeriv w).gradient]
    exact RadialWrapper.carried_gradient_norm hR (frameProjection U) (frameProjection_norm U)
      (gradient Cutoffs.frontier) (fun z => (actual_frontier_bounds z).2.1) w
  · have hb := RadialWrapper.carried_hessian_bound hR frontierHessianBound_nonneg hG.le
      (frameProjection U) (frameProjection_norm U) Cutoffs.frontier (gradient Cutoffs.frontier)
      hbDeriv hbGrad (fun z v => frontier_gradient_lip z v) w
    rw [hratio] at hb
    exact hb
  · have ha := RadialWrapper.wrapped_hessian_bound hR (by nlinarith [h.nonnegative] : 0 ≤ K+8*K^2)
      hG.le (by norm_num : (0:ℝ) ≤ 1/16) (frameProjection U) (frameProjection_norm U)
      (extensive M) (gradient (extensive M)) haDeriv haGrad
      (fun z v => extensive_gradient_norm_sub_le h z v) w
    rw [hratio] at ha
    convert ha using 1
    ring

theorem wrapped_initial_gap_bound {M K CH : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) (w : E) :
    wrappedH CH M U 0-wrappedH CH M U w ≤ (2*(K+2*K^2)+1/2)*(n+1) := by
  let z := fun w => frameProjection U (Bilevel.RadialWrapper.compress (chainRadius CH n) w)
  have ha0 := abs_le.mp (extensive_value_bound h (z 0))
  have haw := abs_le.mp (extensive_value_bound h (z w))
  have hb0 := abs_le.mp (actual_frontier_bounds (z 0)).1
  have hbw := abs_le.mp (actual_frontier_bounds (z w)).1
  change extensive M (z 0)+Cutoffs.frontier (z 0)+(1/16:ℝ)/2*‖(0:E)‖^2-
    (extensive M (z w)+Cutoffs.frontier (z w)+(1/16:ℝ)/2*‖w‖^2) ≤ _
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,add_zero]
  nlinarith [sq_nonneg ‖w‖,Nat.cast_nonneg (α := ℝ) n]

theorem wrapped_bounded_below {M K CH : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) : BddBelow (Set.range (wrappedH CH M U)) := by
  refine ⟨wrappedH CH M U 0-(2*(K+2*K^2)+1/2)*(n+1),?_⟩
  rintro y ⟨w,rfl⟩
  have hg := wrapped_initial_gap_bound (CH := CH) h U w
  linarith

theorem wrapped_initial_infimum_gap {M K CH : ℝ} (h : ActualProfileControl M K)
    {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) :
    wrappedH CH M U 0-sInf (Set.range (wrappedH CH M U)) ≤ (2*(K+2*K^2)+1/2)*(n+1) := by
  have hn : (Set.range (wrappedH CH M U)).Nonempty := ⟨wrappedH CH M U 0,⟨0,rfl⟩⟩
  have hlo : ∀ y ∈ Set.range (wrappedH CH M U),
      wrappedH CH M U 0-(2*(K+2*K^2)+1/2)*(n+1) ≤ y := by
    rintro y ⟨w,rfl⟩
    have hg := wrapped_initial_gap_bound (CH := CH) h U w
    linarith
  have hs := le_csInf hn hlo
  linarith

/-- Concrete source potentials satisfy every bound and the arbitrary-query
barrier, with constants independent of the chain length and ambient frame. -/
theorem actual_wrapped_chain_constants : ∃ CH CAA CBB CΔ : ℝ,
    1 ≤ CH ∧ 0 ≤ CAA ∧ 0 ≤ CBB ∧ 0 ≤ CΔ ∧
    ∀ (n : ℕ) (U : Space n →ₗᵢ[ℝ] E) (w : E),
      |wrappedB CH U w| ≤ 1/4 ∧
      ‖gradient (wrappedB CH U) w‖ ≤ frontierGradientBound ∧
      ‖fderiv ℝ (gradient (wrappedB CH U)) w‖ ≤ CBB ∧
      ‖fderiv ℝ (gradient (wrappedA CH chainAmplitude U)) w‖ ≤ CAA ∧
      wrappedH CH chainAmplitude U 0-wrappedH CH chainAmplitude U w ≤ CΔ*(n+1) ∧
      ((∃ j : Fin (n+1), |frameProjection U (Bilevel.RadialWrapper.compress (chainRadius CH n) w) j| < 1) →
        (1/2:ℝ) ≤ ‖gradient (wrappedH CH chainAmplitude U) w‖) := by
  obtain ⟨K,hK⟩ := actual_profile_control_exists chainAmplitude_nonneg
  let CH := max 1 (K+4*K^2+frontierGradientBound)
  have hCH : 1 ≤ CH := le_max_left _ _
  have hbig : K+4*K^2+frontierGradientBound ≤ CH := le_max_right _ _
  refine ⟨CH,K+8*K^2+1/8,frontierHessianBound+1/16,2*(K+2*K^2)+1/2,
    hCH,by nlinarith [hK.nonnegative],by linarith [frontierHessianBound_nonneg],
    by nlinarith [hK.nonnegative],?_⟩
  intro n U w
  obtain ⟨hb,hbg,hbh,hah⟩ := wrapped_split_uniform_bounds hK hCH hbig U w
  refine ⟨hb,hbg,hbh,hah,wrapped_initial_gap_bound hK U w,?_⟩
  intro hhidden
  apply wrapped_chain_gradient_barrier chainAmplitude_nonneg le_rfl hCH U ?_ w hhidden
  intro z
  exact (chain_gradient_bound hK z).trans (mul_le_mul_of_nonneg_right hbig (Real.sqrt_nonneg _))

end Smoothness2601.ExtensiveChain
