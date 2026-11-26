import Bilevel.ChiFineProfiles
import Bilevel.ZeroChainFlatteningError

/-! Actual incoming-only flattening of the revised centered frontier.
Flattening all latent coordinates agrees exactly: predecessor and tail
selectors are unchanged. The approximation error is independent of length. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainPotential ZeroChainFlatteningCutoff ZeroChainFlatteningMap

def flatProfile (δ t : ℝ) : ℝ := -(phi (flatten δ t)-phi 0)
def flattened (n : ℕ) (δ : ℝ) : Space n → ℝ := selected n (flatProfile δ)

theorem flatProfile_contDiff (δ : ℝ) : ContDiff ℝ 3 (flatProfile δ) :=
  (((phi_contDiff 3).comp (flatten_contDiff δ)).sub contDiff_const).neg

theorem flattened_contDiff (n : ℕ) (δ : ℝ) : ContDiff ℝ 3 (flattened n δ) :=
  selected_contDiff n (flatProfile_contDiff δ)

theorem coordinateCutoff_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16) (t : ℝ) :
    ChiBoundedChain.coordinateCutoff (flatten δ t)=ChiBoundedChain.coordinateCutoff t := by
  by_cases ht : 2*δ≤|t|
  · rw [flatten_identity hδ ht]
  · have hh : |t|≤1/4 := by linarith [lt_of_not_ge ht]
    rw [ChiBoundedChain.coordinateCutoff_zero hh,
      ChiBoundedChain.coordinateCutoff_zero ((flatten_abs_le δ t).trans hh)]

theorem evenGate_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16) (t : ℝ) :
    evenGate (flatten δ t)=evenGate t := by
  by_cases ht : 2*δ≤|t|
  · rw [flatten_identity hδ ht]
  · have hh : |t|≤1/2 := by linarith [lt_of_not_ge ht]
    rw [evenGate_zero hh,evenGate_zero ((flatten_abs_le δ t).trans hh)]

theorem tailMask_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    tailMask i (flattenMap n δ z)=tailMask i z := by
  simp only [tailMask,tailEnergy,flattenMap,coordinateMap_apply,coordinateCutoff_flatten hδ hs]

theorem selector_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    selector n i (flattenMap n δ z)=selector n i z := by
  refine Fin.cases (tailMask_flatten hδ hs 0 z) (fun j => ?_) i
  simp only [selector,Fin.cases_succ,flattenMap,coordinateMap_apply]
  rw [evenGate_flatten hδ hs]
  congr 1
  exact tailMask_flatten hδ hs j.succ z

theorem flattened_eq_latent_composition {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    (n : ℕ) (z : Space n) :
    flattened n δ z=centeredResidual n (flattenMap n δ z) := by
  rw [centered_eq_selected]
  unfold flattened selected
  apply Finset.sum_congr rfl
  intro i _
  change selector n i z*flatProfile δ (z i)=
    selector n i (flattenMap n δ z)* -(phi ((flattenMap n δ z) i)-phi 0)
  rw [selector_flatten hδ hs]
  rfl

theorem flattening_error {δ : ℝ} (hδ : 0<δ) (n : ℕ) (z : Space n) :
    |centeredResidual n z-flattened n δ z|≤2*Real.sqrt (Real.exp 1)*δ := by
  rw [centered_eq_selected,flattened,selected_sub]
  apply selected_abs_bound n (by positivity)
  intro t
  have hh := ZeroChainFlatteningError.child_error_bound hδ t
  convert hh using 1
  · dsimp [flatProfile]
    rw [show -(phi t-phi 0)- -(phi (flatten δ t)-phi 0)=
      -(phi t-phi (flatten δ t)) by ring,abs_neg]

theorem flattened_difference (n : ℕ) (δ' δ : ℝ) :
    (fun z => flattened n δ' z-flattened n δ z)=
      selected n (fun t => -ZeroChainFlatteningAnnulus.resolutionDifference 1 δ' δ t) := by
  funext z
  rw [flattened,flattened,selected_sub]
  congr 1
  funext t
  dsimp [flatProfile,ZeroChainFlatteningAnnulus.resolutionDifference]
  ring

end Bilevel.ChiFine
