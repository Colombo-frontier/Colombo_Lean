import Bilevel.ChiSplitFineProfiles
import Bilevel.ChiFineFlattening

/-! Actual source-only flattening of the split centered frontier. Its value
error is linear in the flattening width, and its unflattened jets are uniform. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiSplitFine
open ChiBoundedChain ZeroChainPotential ZeroChainFlatteningCutoff ZeroChainFlatteningMap

abbrev flatProfile := ChiFine.flatProfile

def flattened (n : ℕ) (δ : ℝ) : Latent n → ℝ := selected n (flatProfile δ)

theorem flatProfile_contDiff (δ : ℝ) : ContDiff ℝ 3 (flatProfile δ) := ChiFine.flatProfile_contDiff δ

theorem flattened_contDiff (n : ℕ) (δ : ℝ) : ContDiff ℝ 3 (flattened n δ) :=
  selected_contDiff n (flatProfile_contDiff δ)

theorem centered_uniform_jet_bound : ∃ M : ℝ,1≤M ∧
    ∀ (n k : ℕ),k≤3 → ∀ z : Latent n,‖iteratedFDeriv ℝ k (ChiSplitChain.frontier n) z‖≤M := by
  obtain ⟨B,hB,hsel⟩ := selector_uniform_jet_bound
  obtain ⟨K,hK,hprof⟩ := chain_profile_bound
  let S := 1+∑ j,B j
  have hS : 1≤S := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hB j))
  have hbS (j : Fin 4) : B j≤S := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hB l) (Finset.mem_univ j)
    dsimp [S]
    linarith
  let f : ℝ → ℝ := fun t => -(phi t-phi 0)
  have hf : ContDiff ℝ 3 f := ((phi_contDiff 3).sub contDiff_const).neg
  have hfb (k : ℕ) (hk : k≤3) (t : ℝ) : |iteratedDeriv k f t|≤2*K := by
    by_cases hz : k=0
    · subst k
      simp only [iteratedDeriv_zero,f,abs_neg]
      have hh := abs_sub (phi t) (phi 0)
      have ha := (hprof 0 t).2
      have hb := (hprof 0 0).2
      simp only [Fin.val_zero,iteratedDeriv_zero] at ha hb
      linarith
    · have he : f=fun t => phi 0-phi t := by funext t;dsimp [f];ring
      rw [he,iteratedDeriv_const_sub (by omega)]
      change |iteratedDeriv k (fun u => -phi u) t|≤2*K
      rw [iteratedDeriv_neg,abs_neg]
      exact ((hprof ⟨k,by omega⟩ t).2).trans (by linarith)
  let D : Fin 4 → ℝ := fun k =>
    ∑ j ∈ Finset.range (k.val+1),(k.val.choose j:ℝ)*S*(2*K)
  have hD (j : Fin 4) : 0≤D j := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  let M := 1+∑ j,D j
  have hM : 1≤M := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hD j))
  have hdM (j : Fin 4) : D j≤M := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hD l) (Finset.mem_univ j)
    dsimp [M]
    linarith
  refine ⟨M,hM,fun n k hk z => ?_⟩
  rw [frontier_eq_selected]
  have hh := selected_jet_bound n hf (fun _ => S) (fun _ => 2*K) (fun _ => by linarith)
    (fun i w j hj => (hsel ⟨j,by omega⟩ n i w).trans (hbS _)) hfb z k hk
  exact hh.trans (hdM ⟨k,by omega⟩)

theorem flattening_error {δ : ℝ} (hδ : 0<δ) (n : ℕ) (z : Latent n) :
    |ChiSplitChain.frontier n z-flattened n δ z|≤2*Real.sqrt (Real.exp 1)*δ := by
  rw [frontier_eq_selected,flattened,selected_sub]
  apply selected_abs_bound n (by positivity)
  intro t
  have hh := ZeroChainFlatteningError.child_error_bound hδ t
  convert hh using 1
  · dsimp [flatProfile,ChiFine.flatProfile]
    rw [show -(phi t-phi 0)- -(phi (flatten δ t)-phi 0)=
      -(phi t-phi (flatten δ t)) by ring,abs_neg]

theorem flattened_difference (n : ℕ) (δ' δ : ℝ) :
    (fun z => flattened n δ' z-flattened n δ z)=
      selected n (fun t => -ZeroChainFlatteningAnnulus.resolutionDifference 1 δ' δ t) := by
  funext z
  rw [flattened,flattened,selected_sub]
  congr 1
  funext t
  dsimp [flatProfile,ChiFine.flatProfile,ZeroChainFlatteningAnnulus.resolutionDifference]
  ring

end Bilevel.ChiSplitFine
