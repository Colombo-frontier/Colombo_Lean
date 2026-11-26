import Bilevel.ChiCarrierRadialProfile
import Bilevel.ChiCarrierJoint

/-! Actual dimension-independent jets for recursive node selectors,
frontier residuals and child release gates at their respective physical widths. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

theorem residualTerm_contDiff (n : ℕ) (i : Fin (n+1)) : ContDiff ℝ 3 (residualTerm n i) :=
  (selector_contDiff n 3 i).neg.mul
    ((ZeroChainPotential.phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)

theorem raw_node_profiles_bound : ∃ B : ℝ,1≤B ∧
    (∀ n (i : Fin (n+1)) z k,k≤3 → ‖iteratedFDeriv ℝ k (ChiBoundedChain.selector n i) z‖≤B) ∧
    (∀ n (i : Fin (n+1)) z k,k≤3 → ‖iteratedFDeriv ℝ k (residualTerm n i) z‖≤B) ∧
    (∀ t k,k≤3 → |iteratedDeriv k releaseGate t|≤B) := by
  obtain ⟨Bs,hBs,hbs⟩ := selector_uniform_jet_bound
  obtain ⟨K,hK,hprofiles⟩ := chain_profile_bound
  obtain ⟨M,hM⟩ := mask_control_exists
  have hM0 : 0≤M := by linarith [hM.one_le]
  have hK0 : 0≤K := by linarith
  have he (k : Fin 4) := ZeroChainResidualCutoffs.plateau_profile_bound releaseGate
    (releaseGate_contDiff (k:=3)) (fun t => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    releaseGate_deriv_compactSupport k.val (show k.val≤3 by omega)
  choose Bq hBq hbq using he
  let Br := fun k : Fin 4 => residualJetBound K M k.val
  have hBr (k : Fin 4) : 0≤Br k := residualJetBound_nonneg hK0 hM0 k.val
  let B := 1+∑ k : Fin 4,(Bs k+Br k+Bq k)
  have hnonneg (k : Fin 4) : 0≤Bs k+Br k+Bq k := add_nonneg (add_nonneg (hBs k) (hBr k)) (hBq k)
  have hsum : 0≤∑ k : Fin 4,(Bs k+Br k+Bq k) := Finset.sum_nonneg (fun k _ => hnonneg k)
  have hB : 1≤B := by unfold B;linarith
  have hBsB (k : Fin 4) : Bs k≤B := by
    have hh := Finset.single_le_sum (fun q (_ : q∈Finset.univ) =>
      hnonneg q) (Finset.mem_univ k)
    unfold B
    linarith [hBr k,hBq k]
  have hBrB (k : Fin 4) : Br k≤B := by
    have hh := Finset.single_le_sum (fun q (_ : q∈Finset.univ) =>
      hnonneg q) (Finset.mem_univ k)
    unfold B
    linarith [hBs k,hBq k]
  have hBqB (k : Fin 4) : Bq k≤B := by
    have hh := Finset.single_le_sum (fun q (_ : q∈Finset.univ) =>
      hnonneg q) (Finset.mem_univ k)
    unfold B
    linarith [hBs k,hBr k]
  refine ⟨B,hB,fun n i z k hk => (hbs ⟨k,by omega⟩ n i z).trans (hBsB ⟨k,by omega⟩),?_,
    fun t k hk => (hbq ⟨k,by omega⟩ t).trans (hBqB ⟨k,by omega⟩)⟩
  intro n i z k hk
  have heq : residualTerm n i=maskedIncoming i := by
    funext y
    exact residualTerm_eq_incoming n i y
  rw [heq]
  exact (maskedIncoming_jet_bound hK0 hM hprofiles i z k hk).trans (hBrB ⟨k,by omega⟩)

theorem constructed_node_jets : ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → D.width≤D.radius → 0<D.parentWidth → D.parentWidth≤D.radius →
      ∀ (i : Fin (D.n+1)) (u : F) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (D.selector i) u‖≤C/D.width^k ∧
      ‖iteratedFDeriv ℝ k (D.residual i) u‖≤C*(D.ell*D.width^2)/D.width^k ∧
      ‖iteratedFDeriv ℝ k D.release u‖≤C/D.parentWidth^k := by
  obtain ⟨B,hB,hs,hr,hq⟩ := raw_node_profiles_bound
  have hB0 : 0≤B := by linarith
  refine ⟨100000*B,by linarith,fun F _ _ _ D hell hh hhR hhp hhpR i u k hk => ?_⟩
  have hsel := scaled_radial_profile_jet_bound (selector_contDiff D.n 3 i)
    B 1 D.width D.radius hB0 (by norm_num) hh hhR
    (fun q hq z => hs D.n i z q hq) D.frame u k hk
  have hres := scaled_radial_profile_jet_bound (residualTerm_contDiff D.n i)
    B (D.ell*D.width^2) D.width D.radius hB0 (by positivity) hh hhR
    (fun q hq z => hr D.n i z q hq) D.frame u k hk
  let p := EuclideanSpace.proj (𝕜:=ℝ) (Fin.last D.n)
  have hqraw : ContDiff ℝ 3 (releaseGate ∘ p) := (releaseGate_contDiff (k:=3)).comp p.contDiff
  have hqbound : ∀ q,q≤3 → ∀ z,‖iteratedFDeriv ℝ q (releaseGate ∘ p) z‖≤B := by
    intro q hqq z
    exact ZeroChainResidualBounds.scalar_linear_jet_bound (releaseGate_contDiff (k:=3)) p
      (ZeroChainResidualBounds.projection_norm_le _) z q hqq B hB0 (hq _ q hqq)
  have hrel := scaled_radial_profile_jet_bound hqraw B 1 D.parentWidth D.radius hB0 (by norm_num)
    hhp hhpR hqbound D.frame u k hk
  refine ⟨?_,?_,?_⟩
  · simpa only [Node.selector,Node.coordinates,Function.comp_def,ZeroChainResidualScaled.scaled,
      one_mul,mul_one] using hsel
  · exact hres
  · have heq : (ZeroChainResidualScaled.scaled (releaseGate ∘ p) 1 D.parentWidth ∘
        WrappedChain.coordinates D.n D.radius D.frame)=D.release := by
      funext v
      change 1*releaseGate (D.parentWidth⁻¹*(D.coordinates v (Fin.last D.n)))=
        releaseGate (D.coordinates v (Fin.last D.n)/D.parentWidth)
      rw [one_mul,div_eq_inv_mul]
    rw [heq] at hrel
    simpa only [mul_one] using hrel

theorem constructed_joint_node_jets : ∃ C : ℝ,1≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → D.width≤D.radius → 0<D.parentWidth → D.parentWidth≤D.radius →
      ∀ (m j : ℕ) (i : Fin (D.n+1)) (x : Blocks m F) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (jointSelector m j D i) x‖≤C/D.width^k ∧
      ‖iteratedFDeriv ℝ k (jointResidual m j D i) x‖≤C*(D.ell*D.width^2)/D.width^k ∧
      ‖iteratedFDeriv ℝ k (jointRelease m j D) x‖≤C/D.parentWidth^k := by
  obtain ⟨C,hC,hb⟩ := constructed_node_jets
  refine ⟨C,hC,fun F _ _ _ D hell hh hhR hhp hhpR m j i x k hk => ?_⟩
  have hs := hb F D hell hh hhR hhp hhpR i (block m j x) k hk
  exact ⟨(block_jet_contraction m j (D.selector_contDiff i 3) x k hk).trans hs.1,
    (block_jet_contraction m j (D.residual_contDiff i 3) x k hk).trans hs.2.1,
    (block_jet_contraction m j (D.release_contDiff 3) x k hk).trans hs.2.2⟩

end Bilevel.ChiCarrier
