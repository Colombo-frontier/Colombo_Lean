import Bilevel.HierarchicalMeanResidual

/-! Dimension-independent jets of the literal globally centered one-sided
residual. The global centering contributes only a numerical zeroth jet. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.HierarchicalMean
open ChiBoundedChain ZeroChainResidualBounds ZeroChainResidualJets ZeroChainPotential

theorem term_jet_selector (n : ℕ) (i : Fin (n+1)) (z : Space n)
    (k : ℕ) (hk : k≤3) (hi : iteratedFDeriv ℝ k (ChiOuter.residualTerm n i) z≠0) :
    ∃ j≤k,iteratedFDeriv ℝ j (ChiOuter.selector n i) z≠0 := by
  by_contra! hz
  apply hi
  have he : ChiOuter.residualTerm n i=fun y => ChiOuter.selector n i y*(-phi (y i)) := by
    funext y
    unfold ChiOuter.residualTerm
    ring
  rw [he]
  exact jet_mul_zero_left (ChiOuter.selector_contDiff n 3 i)
    (((phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff).neg) z k hk hz

theorem term_jets_unique (n : ℕ) (i l : Fin (n+1)) (z : Space n)
    (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (ChiOuter.residualTerm n i) z≠0)
    (hl : iteratedFDeriv ℝ q (ChiOuter.residualTerm n l) z≠0) : i=l := by
  obtain ⟨a,ha,hai⟩ := term_jet_selector n i z k hk hi
  obtain ⟨b,hb,hbl⟩ := term_jet_selector n l z q hq hl
  exact ChiOuter.selector_all_jets_unique i l z a b (by omega) (by omega) hai hbl

theorem normalizedResidual_jet_bounds : ∃ B : ℝ,1≤B ∧ ∀ n k : ℕ,k≤3 →
    ∀ z : Space n, ‖iteratedFDeriv ℝ k (normalizedResidual n) z‖≤B := by
  obtain ⟨C,hC,hterm⟩ := ChiOuter.outer_residual_uniform_jets
  refine ⟨C+|phi 0|,by linarith [abs_nonneg (phi 0)],?_⟩
  intro n k hk z
  have hs : ContDiff ℝ 3 (fun y : Space n => ∑ i : Fin (n+1),ChiOuter.residualTerm n i y) :=
    ContDiff.sum (fun i _ => ChiOuter.outer_residual_contDiff n i)
  have hb : ‖iteratedFDeriv ℝ k
      (fun y : Space n => ∑ i : Fin (n+1),ChiOuter.residualTerm n i y) z‖≤C := by
    rw [iteratedFDeriv_sum (fun i _ => (ChiOuter.outer_residual_contDiff n i).of_le
      (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
    simp only [Finset.sum_apply]
    apply ChiBoundedChain.norm_sum_le_of_exclusive _ C (by linarith)
      (fun i => hterm n i z k hk)
    intro i l hil hi
    by_contra hl
    exact hil (term_jets_unique n i l z k k hk hk hi hl)
  have hc : ‖iteratedFDeriv ℝ k (fun _ : Space n => phi 0) z‖≤|phi 0| := by
    by_cases hk0 : k=0
    · subst k
      simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,le_refl]
    · rw [iteratedFDeriv_const_of_ne hk0]
      simp only [Pi.zero_apply,norm_zero]
      exact abs_nonneg _
  unfold normalizedResidual
  rw [iteratedFDeriv_add_apply' ((hs.of_le (by exact_mod_cast hk)).contDiffAt) contDiffAt_const]
  exact (norm_add_le _ _).trans (add_le_add hb hc)

theorem residual_jet_bounds : ∃ B : ℝ,1≤B ∧ ∀ (n k : ℕ) (L β : ℝ),
    k≤3 → 0≤L → 0<β → ∀ z : Space n,
      ‖iteratedFDeriv ℝ k (residual n L β) z‖≤B*L*β^2/β^k := by
  obtain ⟨B,hB,hb⟩ := normalizedResidual_jet_bounds
  refine ⟨B,hB,fun n k L β hk hL hβ z => ?_⟩
  have h := ZeroChainResidualScaled.scaled_jet_bound (normalizedResidual_contDiff n)
    (L*β^2) β B (by positivity) hβ k hk (hb n k hk) z
  convert h using 1
  ring

theorem wrapped_residual_jet_bounds : ∃ B : ℝ,1≤B ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n k : ℕ) (L β R : ℝ),k≤3 → 0≤L → 0<β → β≤R →
      ∀ (V : Space n →ₗᵢ[ℝ] E) (u : E),
        ‖iteratedFDeriv ℝ k (fun y => residual n L β (WrappedChain.coordinates n R V y)) u‖≤
          B*L*β^2/β^k := by
  obtain ⟨B,hB,hb⟩ := normalizedResidual_jet_bounds
  refine ⟨100000*B,by linarith,fun E _ _ _ n k L β R hk hL hβ hR V u => ?_⟩
  have h := ChiCarrier.scaled_radial_profile_jet_bound (normalizedResidual_contDiff n)
    B (L*β^2) β R (by linarith) (by positivity) hβ hR (fun q hq z => hb n q hq z) V u k hk
  convert h using 1
  ring

end Bilevel.HierarchicalMean
