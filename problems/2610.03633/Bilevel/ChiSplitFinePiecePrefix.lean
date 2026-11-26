import Bilevel.ChiSplitFinePrefix

/-! Actual scaled split fine pieces and their normal coupling are evaluable
from the next source prefix and the old predecessor prefix. -/
noncomputable section
open scoped BigOperators Topology
namespace Bilevel.ChiSplitFine
open ChiBoundedChain PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ZeroChainSchedule

theorem approximation_prefix_value (n J : ℕ) (δ : ℕ → ℝ) (j r : ℕ) (z : Latent n)
    (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|≤1/4) :
    approximation n J δ j z=approximation n J δ j (retainSplit n r z) := by
  by_cases hj : j<J
  · simp only [approximation,if_pos hj,flattened]
    exact selected_prefix_value _ r z hb
  · simp only [approximation,if_neg hj,frontier_eq_selected]
    exact selected_prefix_value _ r z hb

theorem piece_prefix_value (n J : ℕ) (δ : ℕ → ℝ) (j r : ℕ) (z : Latent n)
    (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|≤1/4) :
    piece n J δ j z=piece n J δ j (retainSplit n r z) := by
  cases j with
  | zero => exact approximation_prefix_value n J δ 0 r z hb
  | succ j => simp only [piece,approximation_prefix_value n J δ (j+1) r z hb,approximation_prefix_value n J δ j r z hb]

theorem pieces_prefix_value (P : ChiFine.Parameters) (n j r : ℕ) (z : Latent n)
    (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|≤P.β/4) :
    pieces P n j z=pieces P n j (retainSplit n r z) := by
  have hβ := P.β_pos
  have hs : ∀ i : Fin (n+1),r≤ i.val → |(P.β⁻¹ • z).snd i|≤1/4 := by
    intro i hi
    change |P.β⁻¹*z.snd i|≤1/4
    rw [abs_mul,abs_inv,abs_of_pos hβ]
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hβ).mpr (by linarith only [hb i hi])
  have he := piece_prefix_value n (levels P.θ) (resolution P.c 1 P.θ) j r (P.β⁻¹ • z) hs
  rw [(retainSplit n r).map_smul P.β⁻¹ z] at he
  exact congrArg (fun v : ℝ => P.amplitude*v) he

theorem value_prefix_eventually {n : ℕ} (f : Latent n → ℝ) (r : ℕ) (τ : ℝ)
    (hv : ∀ z : Latent n,(∀ i : Fin (n+1),r≤ i.val → |z.snd i|≤τ) → f z=f (retainSplit n r z))
    (z : Latent n) (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|<τ) :
    f =ᶠ[𝓝 z] f ∘ retainSplit n r := by
  have ho : IsOpen {w : Latent n | ∀ i : Fin (n+1),r≤ i.val → |w.snd i|<τ} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp
      (jointSndLinear : Latent n →L[ℝ] Space n).continuous).abs) continuous_const
  filter_upwards [ho.mem_nhds hb] with w hw
  exact hv w (fun i hi => (hw i hi).le)

theorem pieces_prefix_fderiv (P : ChiFine.Parameters) (n j r : ℕ) (z : Latent n)
    (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|<P.β/4) :
    fderiv ℝ (pieces P n j) z=fderiv ℝ (pieces P n j ∘ retainSplit n r) z :=
  (value_prefix_eventually _ r (P.β/4) (pieces_prefix_value P n j r) z hb).fderiv_eq

theorem pieces_prefix_gradient (P : ChiFine.Parameters) (n j r : ℕ) (z : Latent n)
    (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|<P.β/4) :
    gradient (pieces P n j) z=gradient (pieces P n j ∘ retainSplit n r) z := by
  have hg := (((pieces_contDiff P n j).comp (retainSplit n r).contDiff).differentiable (by norm_num) z).hasGradientAt
  exact (hg.congr_of_eventuallyEq
    (value_prefix_eventually _ r (P.β/4) (pieces_prefix_value P n j r) z hb)).gradient

theorem coupling_prefix_value (P : ChiFine.Parameters) (n r : ℕ) (s t : ℝ) (z : Latent n)
    (hb : ∀ i : Fin (n+1),r≤ i.val → |z.snd i|≤P.β/4) :
    (data P n).coupling (CompensatedMean.pack (Latent n) z s t)=
      (data P n).coupling (CompensatedMean.pack (Latent n) (retainSplit n r z) s t) := by
  simp only [CompensatedMean.Data.coupling,CompensatedMean.Data.couplingTerm,
    CompensatedMean.uProj_pack,CompensatedMean.sProj_pack,data]
  apply Finset.sum_congr rfl
  intro j _
  rw [pieces_prefix_value P n j r z hb]

end Bilevel.ChiSplitFine
